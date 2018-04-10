{-# LANGUAGE TemplateHaskell #-}
module Solver.Chc where


import           Control.Lens
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Grammar (Grammar, NT, Rule)
import qualified Data.Grammar as G
import           Data.Semigroup

import           Formula.Expr
import           Formula.Var

-- | A fragment of a constrained Horn Clause rule.
data Fragment
  = Capture Var
  | Uncapture
  | Apply Var
  | Fact Expr
  deriving (Show, Read, Eq, Ord)

type Chc = Grammar Fragment

scope :: Var -> Rule Fragment -> Rule Fragment
scope v r = G.Terminal (Capture v) <> r <> G.Terminal Uncapture

type ProofStructure = Grammar Proof

data Proof
  = Continue
  | Entails (Map NT (Set NT)) NT (Rule Fragment)
  deriving (Show, Read, Eq, Ord)

class Monad m => Expandable m where
  getProof :: m ProofStructure
  getClones :: m (Map NT (Set NT))

data ChcState = ChcState
  { _varMapping :: [(Var, Var)]
  , _varQueue :: Seq Var
  , _varCounter :: Int
  } deriving (Show, Read, Eq, Ord)
makeLenses ''ChcState

emptyChcState :: ChcState
emptyChcState = ChcState
  { _varMapping = []
  , _varQueue = Seq.empty
  , _varCounter = 0
  }

generativeResolve :: Monad m => Fragment -> StateT ChcState m Expr
generativeResolve = \case
  Apply v -> do
    -- Applying a variable adds the variable to the vocabulary and has a
    -- trivial proof.
    m <- use varMapping
    varQueue %= (Seq.<|) (subst' m v)
    pure (LBool True)
  Capture v -> do
    -- Capturing a variable either yields fresh variables or pops the
    -- vocabulary. The proof is trivial.
    Seq.viewr <$> use varQueue >>= \case
      Seq.EmptyR -> do
        v' <- freshVar v
        varMapping %= (:) (v, v')
      (xs Seq.:> x) -> do
        varQueue .= xs
        varMapping %= (:) (v, x)
    pure (LBool True)
  Uncapture -> do
    -- Uncapture does nothing but change the vocabulary context. The proof
    -- is trivial.
    varMapping %= tail
    pure (LBool True)
  Fact e ->
    -- A single fact unwinds by applying the current vocabulary to the
    -- fact. The proof is trivial.
    applyMapping e

simpleResolve :: Monad m => Fragment -> StateT ChcState m Expr
simpleResolve = \case
  Apply v -> do
    -- Applying a variable adds the variable to the vocabulary and has a
    -- trivial proof.
    m <- use varMapping
    varQueue %= (Seq.<|) (subst' m v)
    pure (LBool True)
  Capture v -> do
    -- Capturing a variable either yields fresh variables or pops the
    -- vocabulary. The proof is trivial.
    Seq.viewr <$> use varQueue >>= \case
      Seq.EmptyR -> pure ()
      (xs Seq.:> x) -> do
        varQueue .= xs
        varMapping %= (:) (v, x)
    pure (LBool True)
  Uncapture ->
    -- Uncapture does nothing but change the vocabulary context. The proof
    -- is trivial.
    -- varMapping %= tail
    pure (LBool True)
  Fact e ->
    -- A single fact unwinds by applying the current vocabulary to the
    -- fact. The proof is trivial.
    applyMapping e

applyMapping :: MonadState ChcState m => Expr -> m Expr
applyMapping e = do
  m <- use varMapping
  pure (subst' m e)

freshVar :: MonadState ChcState m => Var -> m Var
freshVar v = do
  c <- use varCounter
  varCounter += 1
  pure (v & varName <>~ ("%" ++ show c))

subst' :: Data a => [(Var, Var)] -> a -> a
subst' vs = subst (foldr (uncurry M.insert) M.empty vs)
