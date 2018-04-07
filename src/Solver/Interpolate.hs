module Solver.Interpolate where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Reader

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Grammar (Grammar, Rule, NT)
import qualified Data.Grammar as G
import           Data.Maybe (fromMaybe)

import           Formula
import qualified Formula.Z3 as Z3

import Data.Text.Prettyprint.Doc

topologicalInterpolation :: MonadIO m => Grammar Expr -> m (Either Model (Map NT Expr))
topologicalInterpolation g =
  let nts = G.topologicalOrder g
  in runStateT (loop nts) M.empty >>= \case
    (Left m, _) -> pure (Left m)
    (_, m) -> pure (Right m)
  where
    loop :: MonadIO m => [NT] -> StateT (Map NT Expr) m (Either Model ())
    loop [] = pure (Right ())
    loop (nt:nts) = interpolateNT' nt g >>= \case
      Left m -> pure (Left m)
      _ -> loop nts

interpolateNT' :: MonadIO m => NT -> Grammar Expr -> StateT (Map NT Expr) m (Either Model ())
interpolateNT' target g = do
  solns <- get
  interpolateNT target solns g >>= \case
    Left m -> pure (Left m)
    Right phi -> modify (M.insert target phi) >> pure (Right ())

-- | Interpolate the given nonterminal in the context of the directly solvable grammar.
interpolateNT :: MonadIO m => NT -> Map NT Expr -> Grammar Expr -> m (Either Model Expr)
interpolateNT target solns g =
  let (phi1, phi2) = interpolationForms target solns g
  in Z3.interpolate phi1 phi2

-- | Find the two formulas on either side of the target nonterminal. The two
-- formulas are found by partitioning the grammar at the location of the
-- nonterminal.
interpolationForms :: NT -> Map NT Expr -> Grammar Expr -> (Expr, Expr)
interpolationForms target solns g =
  let (reaching, reached) = G.partition [target] g
  in ( grammarExpr target solns reaching
     , grammarExpr target solns reached)

-- | Find the formula for the given grammar.
grammarExpr :: NT -> Map NT Expr -> Grammar Expr -> Expr
grammarExpr target solns g =
  let nts = S.toList $ S.delete target $ G.nonterminals g
      ntPhi = map (\nt -> productionExpr solns nt (G.ruleFor nt g)) nts
  in manyAnd (ruleExpr solns (G.start g) : ntPhi)

-- | Find the formula for the given production.
productionExpr :: Map NT Expr -> NT -> Rule Expr -> Expr
productionExpr solns nt r = mkImpl (nontermExpr solns nt) (ruleExpr solns r)

-- | Find the formula for the given rule.
ruleExpr :: Map NT Expr -> Rule Expr -> Expr
ruleExpr solns = go
  where
    go = \case
      G.Null -> LBool False
      G.Eps -> LBool True
      G.Alt a b -> mkOr (go a) (go b)
      G.Seq a b -> mkAnd (go a) (go b)
      G.Terminal t -> t
      G.Nonterminal nt -> nontermExpr solns nt

-- | Find the formula for the given nonterminal. If the definition is known,
-- the formula is the definition. Otherwise, it is a representative boolean
-- variable.
nontermExpr :: Map NT Expr -> NT -> Expr
nontermExpr solns nt@(G.NT c) =
  fromMaybe (V $ Var ("__b" ++ show c) Bool) (mkNot <$> M.lookup nt solns)
