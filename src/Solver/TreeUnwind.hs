{-# LANGUAGE TemplateHaskell #-}
module Solver.TreeUnwind where

import           Control.Lens hiding (mapping)
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Arrow (second)
import           Control.Applicative

import           Data.Data (Data)
import           Data.Semigroup
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Grammar (Grammar, NT, Rule)
import qualified Data.Grammar as G
import           Data.InfGrammar (InfGrammar, InfRule)
import qualified Data.InfGrammar as IG

import           Formula hiding (Rule, Chc)

import           Solver.Types hiding (DirectState(..))
import           Solver.Chc
import           Solver.Interpolate

import Debug.Trace

data UnwindState = UnwindState
  { _ntCounter :: Int
  , _clones :: Map NT (Set NT)
  , _proofStart :: Rule Proof
  , _proofRules :: Map NT (Rule Proof)
  , _chcState :: ChcState
  , _descendants :: Map NT (Map NT (Set NT))
  } deriving (Show, Read, Eq, Ord)

data UnwindCtxt = UnwindCtxt
  { _visited :: Set NT
  , _branchClones :: Map NT (Set NT)
  , _left :: Maybe (NT, NT)
  , _currentRule :: Rule Fragment
  , _chcSystem :: Chc
  } deriving (Show, Read, Eq, Ord)

makeLenses ''UnwindState
makeLenses ''UnwindCtxt

emptyState :: UnwindState
emptyState = UnwindState
  { _ntCounter = 0
  , _clones = M.empty
  , _proofStart = G.Null
  , _proofRules = M.empty
  , _chcState = emptyChcState
  , _descendants = M.empty
  }

emptyCtxt :: UnwindCtxt
emptyCtxt = UnwindCtxt
  { _visited = S.empty
  , _branchClones = M.empty
  , _left = Nothing
  , _currentRule = mempty
  , _chcSystem = mempty
  }

instance Monad m => Expandable (StateT UnwindState m) where
  getProof = G.mkGrammar <$> use proofStart <*> use proofRules
  getClones = use clones

instance Expandable m => Expandable (ReaderT UnwindCtxt m) where
  getProof = lift getProof
  getClones = lift getClones

-- | Unwind the given CHC system to a tree.
-- In addition, generate a proof structure which indicates what an inductive
-- proof for the grammar would look like.
-- The proof structure is encoded in the state. As the user unwind
treeUnwind :: (MonadReader UnwindCtxt m, MonadState UnwindState m)
           => Chc -> m (InfGrammar m Expr)
treeUnwind chc =
  local ((chcSystem .~ chc) . (currentRule .~ G.start chc)) (unwindFrom (G.start chc))

unwindFrom :: (MonadReader UnwindCtxt m, MonadState UnwindState m)
           => Rule Fragment -> m (InfGrammar m Expr)
unwindFrom r = do
  (g, p) <- local (currentRule .~ r) (unw r)
  lhs <- view left
  case lhs of
    Nothing -> proofStart .= p
    Just (_, nt') -> proofRules %= M.insertWith G.alt nt' p
  pure g
  where
    unw :: (MonadReader UnwindCtxt m, MonadState UnwindState m)
        => Rule Fragment
        -> m (InfGrammar m Expr, Rule Proof)
    unw = \case
      G.Null ->
        -- Unwinding a null rule yields null, and a proof is impossible.
        pure (empty, empty)
      G.Eps ->
        -- Unwinding an eps rule yields eps, and the proof is trivial.
        pure mempty
      G.Seq x y ->
        -- Unwinding a sequence requires unwinding both parts and proving both parts.
        (<>) <$> unw x <*> unw y
      G.Alt x y -> do
        -- Unwinding an alternation requires unwinding both parts with the same
        -- vocabulary.  A proof must show both branches.
        q <- use chcState
        (x', px) <- unw x
        chcState .= q
        (y', py) <- unw y
        pure (x' <|> y', px <> py)
      G.Terminal x -> do
        st <- use chcState
        let (x', st') = runState (generativeResolve x) st
        chcState .= st'
        pure (case x' of
          LBool True -> G.epsGrammar
          _ -> G.singleton (IG.Finite x'), mempty)
      G.Nonterminal nt -> do
        -- Nonterminals are the most complex rules to unwind.
        -- First, there are two possibilities:
        --  If we have seen the nonterminal before in the current unwinding, then
        --  we should not unwind further until later.
        --  Otherwise, we should unwind the rule for that nonterminal now.
        -- The proof for a nonterminal can be shown by giving an inductive
        -- invocation by using a descendant with the same location or by
        -- showing its rule is inductive.

        -- Construct a fresh copy of the nonterminal.
        chc <- view chcSystem
        nt' <- freshNT nt
        -- Add proof branches which allow the prover to show a descendant entails this.
        addDescs nt nt'
        vis <- view visited
        g <- context nt nt' $
          if nt `elem` vis
          -- We've seen the base nonterminal before in the current branch,
          -- so construct a recursive, rolled subgrammar.
          then do
            view left >>= \case
              Nothing -> pure ()
              Just (lhs, lhs') -> do
                descs <- M.findWithDefault M.empty nt' <$> use descendants
                rule <- view currentRule
                proofRules %= M.insertWith G.alt nt' (pure (Entails descs lhs rule))
            -- ps <- M.findWithDefault G.Null nt' <$> use proofRules
            let ac = local (chcSystem .~ chc) ((proofRules %= M.delete nt') >> context nt nt' (unwindFrom (G.ruleFor nt chc)))
            -- let ac = local (visited .~ mempty) (context nt nt' (unwindFrom (G.ruleFor nt chc)))
            pure (G.singleton (IG.Infinite ac))
          -- We have not seen the base nonterminal in the current branch,
          -- so unwind it now and add its unwinding as a possible
          -- proof strategy.
          else do
            (g', p) <- local ( (currentRule .~ G.ruleFor nt chc)
                             . (left .~ Just (nt, nt'))
                             ) (unw (G.ruleFor nt chc))
            proofRules %= M.insertWith G.alt nt' p
            pure g'
        pure (G.abstract nt' g, G.Nonterminal nt')
    -- Perform the action in a context where the given base nonterminal has been visited and
    -- where the current branch has a clone for the base nonterminal as specified.
    context nt nt' ac = do
      ds <- use descendants
      local ( (visited %~ S.insert nt)
            . (branchClones .~ M.findWithDefault M.empty nt' ds)
            . (left .~ Just (nt, nt'))) ac

addDescs :: (MonadReader UnwindCtxt m, MonadState UnwindState m) => NT -> NT -> m ()
addDescs nt nt' = do
  preds <- view branchClones
  descendants %= M.unionWith (M.unionWith S.union) (M.singleton nt' preds)
  descendants %= M.unionWith (M.unionWith S.union) (M.singleton nt' (M.singleton nt (S.singleton nt')))

freshNT :: MonadState UnwindState m => NT -> m NT
freshNT (G.NT nt) = do
  new <- use ntCounter
  ntCounter += 1
  clones %= M.insertWith S.union (G.NT nt) (S.singleton (G.NT new))
  pure (G.NT new)
