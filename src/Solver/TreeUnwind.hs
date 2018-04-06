{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module Solver.TreeUnwind where

import           Control.Lens hiding (mapping)
import           Control.Monad.State
import           Control.Monad.Reader
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

import Data.Text.Prettyprint.Doc

import Debug.Trace

data UnwindState = UnwindState
  { _ntCounter :: Int
  , _varCounter :: Int
  , _clones :: Map NT (Set NT)
  , _proofStart :: Rule Proof
  , _proofRules :: Map NT (Rule Proof)
  , _varQueue :: Seq Var
  , _varMapping :: [(Var, Var)]
  , _descendants :: Map NT (Map NT (Set NT))
  } deriving (Show, Read, Eq, Ord)

data UnwindCtxt = UnwindCtxt
  { _visited :: Set NT
  , _branchClones :: Map NT (Set NT)
  } deriving (Show, Read, Eq, Ord)

makeLenses ''UnwindState
makeLenses ''UnwindCtxt

emptyState :: UnwindState
emptyState = UnwindState
  { _ntCounter = 0
  , _varCounter = 0
  , _clones = M.empty
  , _proofStart = G.Null
  , _proofRules = M.empty
  , _varQueue = Seq.empty
  , _varMapping = []
  , _descendants = M.empty
  }

emptyCtxt :: UnwindCtxt
emptyCtxt = UnwindCtxt
  { _visited = S.empty
  , _branchClones = M.empty
  }

instance Monad m => Expandable (StateT UnwindState m) where
  getProof = G.mkGrammar <$> use proofStart <*> use proofRules
  getClones = use clones

-- | Unwind the given CHC system to a tree.
-- In addition, generate a proof structure which indicates what an inductive
-- proof for the grammar would look like.
-- The proof structure is encoded in the state. As the user unwind
treeUnwind :: (MonadReader UnwindCtxt m, MonadState UnwindState m)
           => Chc -> m (InfGrammar m Expr)
treeUnwind chc = unwindFrom Nothing chc (G.start chc)

unwindFrom :: (MonadReader UnwindCtxt m, MonadState UnwindState m)
           => Maybe NT -> Chc -> Rule Fragment -> m (InfGrammar m Expr)
unwindFrom nt chc r = do
  (g, p) <- unw r
  case nt of
    Nothing -> proofStart .= p
    Just nt' -> proofRules %= M.insertWith G.alt nt' p
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
        q <- use varQueue
        (x', px) <- unw x
        varQueue .= q
        (y', py) <- unw y
        pure (x' <|> y', px <> py)
      G.Terminal (Apply v) -> do
        -- Applying a variable adds the variable to the vocabulary and has a
        -- trivial proof.
        m <- use varMapping
        varQueue %= (Seq.<|) (subst' m v)
        pure mempty
      G.Terminal (Capture v) -> do
        -- Capturing a variable either yields fresh variables or pops the
        -- vocabulary. The proof is trivial.
        Seq.viewr <$> use varQueue >>= \case
          Seq.EmptyR -> do
            v' <- freshVar v
            varMapping %= (:) (v, v')
          (xs Seq.:> x) -> do
            varQueue .= xs
            varMapping %= (:) (v, x)
        pure mempty
      G.Terminal Uncapture -> do
        -- Uncapture does nothing but change the vocabulary context. The proof
        -- is trivial.
        varMapping %= tail
        pure mempty
      G.Terminal (Fact e) -> do
        -- A single fact unwinds by applying the current vocabulary to the
        -- fact. The proof is trivial.
        m <- use varMapping
        pure (G.singleton (IG.Finite (subst' m e)), mempty)
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
        nt' <- freshNT nt
        -- Add proof branches which allow the prover to show a descendant entails this.
        handleDescs nt nt'
        vis <- view visited
        context nt nt' $
          if nt `elem` vis
          -- We've seen the base nonterminal before in the current branch,
          -- so construct a recursive, rolled subgrammar.
          then do
            ps <- M.findWithDefault G.Null nt' <$> use proofRules
            proofRules %= M.delete nt'
            let ac = context nt nt' $ do
                  proofRules %= M.insertWith G.alt nt' ps
                  unwindFrom (Just nt') chc (G.ruleFor nt chc)
            pure (G.abstract nt' $ G.singleton (IG.Infinite ac), G.Nonterminal nt')
          -- We have not seen the base nonterminal in the current branch,
          -- so unwind it now and add its unwinding as a possible
          -- proof strategy.
          else do
            (g', p) <- unw (G.ruleFor nt chc)
            proofRules %= M.insertWith G.alt nt' p
            pure (G.abstract nt' g', G.Nonterminal nt')
    -- Perform the action in a context where the given base nonterminal has been visited and
    -- where the current branch has a clone for the base nonterminal as specified.
    context nt nt' ac = do
      ds <- use descendants
      local ( (visited %~ S.insert nt)
            . (branchClones .~ M.findWithDefault M.empty nt' ds)) ac

handleDescs :: (MonadReader UnwindCtxt m, MonadState UnwindState m) => NT -> NT -> m ()
handleDescs nt nt' = do
  preds <- view branchClones
  descendants %= M.unionWith (M.unionWith S.union) (M.singleton nt' preds)
  descs <- use descendants
  descendants %= M.unionWith (M.unionWith S.union) (M.singleton nt' (M.singleton nt (S.singleton nt')))
  ds <- pure (M.findWithDefault S.empty nt (M.findWithDefault M.empty nt' descs))
  mapM_ (\d -> proofRules %= M.insertWith G.alt nt' (pure (Entails d nt'))) ds

freshVar :: MonadState UnwindState m => Var -> m Var
freshVar v = do
  c <- use varCounter
  varCounter += 1
  pure (v & varName <>~ ("%" ++ show c))

freshNT :: MonadState UnwindState m => NT -> m NT
freshNT (G.NT nt) = do
  new <- use ntCounter
  ntCounter += 1
  clones %= M.insertWith S.union (G.NT nt) (S.singleton (G.NT new))
  pure (G.NT new)

subst' :: Data a => [(Var, Var)] -> a -> a
subst' vs = subst (foldr (uncurry M.insert) M.empty vs)

test :: Chc
test =
  G.mkGrammar
  (  G.Terminal (Fact [expr|x = 41|])
  <> G.Terminal (Apply x)
  <> G.Nonterminal 0
  ) $
  M.fromList
    [ (0, scope x (G.Terminal (Fact [expr|x = 0|]))
      <|> scope x' (scope x $ G.Terminal (Fact [expr|x' = x+2|])
                               <> G.Terminal (Apply x)
                               <> G.Nonterminal 0))
    ]
  where
    x = Var "x" Int
    x' = Var "x'" Int

experiment :: IO ()
experiment = runReaderT (evalStateT ( do
  g <- treeUnwind test
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g)

  g' <- IG.unroll S.empty g
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g')
  g'' <- IG.unroll S.empty g'
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g'')

  g''' <- IG.unroll S.empty g''
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g''')

  p <- getProof
  liftIO $ print $ G.topologicalOrder p
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw p)
  ) emptyState) emptyCtxt
