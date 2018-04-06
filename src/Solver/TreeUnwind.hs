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

data UnwindState = UnwindState
  { _ntCounter :: Int
  , _varCounter :: Int
  , _clones :: Map NT (Set NT)
  , _proofStructure :: ProofStructure
  , _varQueue :: Seq Var
  , _varMapping :: [(Var, Var)]
  }
makeLenses ''UnwindState

emptyState :: UnwindState
emptyState = UnwindState
  { _ntCounter = 0
  , _varCounter = 0
  , _clones = M.empty
  , _proofStructure = G.nullGrammar
  , _varQueue = Seq.empty
  , _varMapping = []
  }

-- Unwind the given CHC system to a tree. In addition, rename the variables in
-- the query to be consistent with the new CHC vocabulary and generate a map
-- from symbols in the original grammar to symbols in the new grammar.
treeUnwind :: MonadState UnwindState m => Chc -> m (InfGrammar m Expr)
treeUnwind chc = unwindFrom S.empty chc (G.start chc)

unwindFrom :: MonadState UnwindState m
           => Set NT -> Chc -> Rule Fragment -> m (InfGrammar m Expr)
unwindFrom vis chc r = do
  (st, rs) <- runStateT (runReaderT (unw r) vis) M.empty
  pure (G.mkGrammar st rs)
  where
    unw :: MonadState UnwindState m
        => Rule Fragment
        -> ReaderT (Set NT) (StateT (Map NT (InfRule m Expr)) m) (InfRule m Expr)
    unw = \case
      G.Null -> pure G.Null
      G.Eps -> pure G.Eps
      G.Seq x y -> (<>) <$> unw x <*> unw y
      G.Alt x y -> do
        q <- unwind (use varQueue)
        x' <- unw x
        unwind (varQueue .= q)
        y' <- unw y
        pure (x' <|> y')
      G.Nonterminal nt -> do
        nt' <- unwind $ freshNT nt
        vis <- ask
        if nt `elem` vis
        then do let r = IG.inf (unwindFrom (S.singleton nt) chc (G.ruleFor nt chc))
                modify (M.insert nt' r)
        else do
          r <- local (S.insert nt) (unw (G.ruleFor nt chc))
          modify (M.insert nt' r)
        pure (G.Nonterminal nt')
      G.Terminal (Apply v) -> unwind (do
        m <- use varMapping
        varQueue %= (Seq.<|) (subst' m v)
        pure G.Eps)
      G.Terminal (Capture v) -> do
        Seq.viewr <$> unwind (use varQueue) >>= \case
          Seq.EmptyR -> unwind (do
            v' <- freshVar v
            varMapping %= (:) (v, v'))
          (xs Seq.:> x) -> unwind (do
            varQueue .= xs
            varMapping %= (:) (v, x))
        pure G.Eps
      G.Terminal Uncapture -> unwind (do
        varMapping %= tail
        pure G.Eps)
      G.Terminal (Fact e) -> do
        m <- unwind (use varMapping)
        pure (IG.fin (subst' m e))
    unwind = lift . lift

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
experiment = evalStateT ( do
  g <- treeUnwind test
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g)
  g' <- IG.unroll S.empty g
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g')
  g'' <- IG.unroll S.empty g'
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g'')
  ) emptyState
