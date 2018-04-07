module Solver.Shara where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Applicative

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Maybe (isJust, fromJust)
import           Data.Semigroup
import           Data.List.Split

import           Formula hiding (Chc)
import qualified Formula.Z3 as Z3

import           Data.Grammar (Grammar, Rule, NT)
import qualified Data.Grammar as G

import           Data.InfGrammar (InfGrammar)
import qualified Data.InfGrammar as IG

import           Solver.Types
import           Solver.Interpolate
import           Solver.Chc
import           Solver.TreeUnwind

-- | Encode the CHC as a (possibly infinite) unrollable grammar such that each
-- unrolling is a directly solvable CHC system.
-- directlySolvable :: Expandable m => Chc -> m (InfGrammar m Expr)
-- directlySolvable = treeUnwind

-- | Apply the interpolator to the given directly solvable system and yield
-- either a counterexample model or solutions for the nonterminals.
solveDirect :: MonadIO m => Grammar Expr -> m (Either Model (Map NT Expr))
solveDirect = topologicalInterpolation

-- | Solve the Relational Post Fixed-Point Problem as encoded by the given CHC
-- system.
-- solveChc :: (Expandable m, MonadIO m) => Chc -> m (Either Model (Map NT Expr))
solveChc chc = solve =<< treeUnwind chc

treeSolve :: Chc -> IO (Either Model (Map NT Expr))
treeSolve chc = evalStateT (runReaderT (solve =<< treeUnwind chc) emptyCtxt) emptyState

solve :: (Expandable m, MonadIO m) => InfGrammar m Expr -> m (Either Model (Map NT Expr))
solve g = solveDirect (IG.finite g) >>= \case
  Left m -> pure (Left m)
  Right sol -> do
    ps <- getProof
    (mproof, indSet) <- inductive ps sol
    case mproof of
      Just proof -> do
        cs <- getClones
        let sol' = M.filterWithKey (\k _ -> k `elem` G.nonterminals proof) sol
        pure (Right (collapse cs sol'))
      Nothing -> IG.unroll indSet g >>= solve

-- | Given the solution to an interpolation of the grammar and the proof structure,
-- determine which nonterminals are inductive.
inductive :: MonadIO m => ProofStructure -> Map NT Expr -> m (Maybe ProofStructure, Set NT)
inductive ps sols = do
  (res, m) <- runStateT (ind (G.start ps)) M.empty
  -- Discard parts of proof which weren't inductive.
  let m' = M.map fromJust $ M.filter isJust m
  -- Construct a proof, but only if the start was inductive.
  let proof = G.mkGrammar <$> res <*> pure m'
  pure (proof, M.keysSet m')
  where
    -- | Check that a given proof rule is inductive.
    ind :: MonadIO m => Rule Proof -> StateT (Map NT (Maybe (Rule Proof))) m (Maybe (Rule Proof))
    ind = \case
      -- A null rule is automatically not inductive.
      G.Null -> pure Nothing
      -- An empty rule is automatically inductive.
      G.Eps -> pure (Just G.Eps)
      -- For seq, both subrules must be inductive.
      G.Seq x y -> (<>) <$> ind x <*> ind y
      -- For alt, either subrule being inductive is fine.
      G.Alt x y -> (<|>) <$> ind x <*> ind y
      -- If a portion of the proof is rolled, it is not inductive.
      G.Terminal Continue -> pure Nothing
      -- The terminal's inductiveness is contingent on some logical entailment.
      G.Terminal (Entails nt nt') ->
        entails (M.findWithDefault (LBool True) nt sols)
                (M.findWithDefault (LBool False) nt' sols) >>= \case
          False -> pure Nothing
          True -> pure (Just $ G.Terminal (Entails nt nt'))
      -- The nonterminal is inductive if it was previously found to be or if
      -- its rule is inductive.
      G.Nonterminal nt ->
        M.lookup nt <$> get >>= \case
          Just _ -> pure (Just $ G.Nonterminal nt)
          Nothing -> do
            sol <- ind (G.ruleFor nt ps)
            at nt ?= sol
            case sol of
              Nothing -> pure Nothing
              Just _ -> pure (Just $ G.Nonterminal nt)

cut :: Grammar a -> (Set NT, Set NT, Set NT)
cut = undefined

entails :: MonadIO m => Expr -> Expr -> m Bool
entails e1 e2 = unalias e1 `Z3.entails` unalias e2
  where
    unalias :: Expr -> Expr
    unalias e = e & vars . varName %~ unal
    unal :: String -> String
    unal n = head (splitOn "%" n)

collapse :: Map NT (Set NT) -> Map NT Expr -> Map NT Expr
collapse _ = id -- TODO
