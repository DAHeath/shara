module Shara.Shara where

import           Control.Lens
import           Control.Monad.State
import           Data.List.Split     (splitOn)
import           Data.Map            (Map)
import qualified Data.Map            as M
import           Data.Set            (Set)
import qualified Data.Set            as S
import           Formula
import qualified Formula.Z3          as Z3
import           Shara.CDD
import           Shara.Grammar
import           Shara.Interpolate
import qualified Shara.Reg           as R

data SolveKind
  = Topological
  | LicketySplit InterpolationStrategy
  deriving (Show, Read, Eq, Ord)

shara ::
     MonadIO m
  => SolveKind
  -> Map NT [Var]
  -> SGrammar [Var] Expr
  -> m (Either Model (Map NT Expr))
shara sk vocab sg = evalStateT (go =<< cdd sg) (emptyCDDState vocab)
  where
    go g = do
      solveDirect sk (finitePrefix g) >>= \case
        Left m -> pure (Left m)
        Right m -> do
          cs <- use clones
          let sol = collapse cs m
          inductive vocab sol sg >>= \case
            Nothing -> pure (Right sol)
            Just inds -> go =<< unrollCDD g {- inds -}

solveDirect ::
     MonadIO m => SolveKind -> Grammar Expr -> m (Either Model (Map NT Expr))
solveDirect =
  \case
    Topological -> topologicalInterpolation
    LicketySplit strat -> licketySplit strat

inductive ::
     MonadIO m
  => Map NT [Var]
  -> Map NT Expr
  -> SGrammar [Var] Expr
  -> m (Maybe (Set NT))
inductive vars sols g = do
  s <- (S.fromList . concat) <$> M.traverseWithKey indRule (rules g)
  pure $
    if null (nonterminals g S.\\ s)
      then Nothing
      else Just s
  where
    indRule :: MonadIO m => NT -> SRule [Var] Expr -> m [NT]
    indRule nt r =
      let cons = M.findWithDefault (LBool False) nt sols
          ante = expr r
      in Z3.entails ante cons >>= \case
           True -> pure [nt]
           False -> pure []
    expr =
      \case
        R.Seq x y -> mkAnd (expr x) (expr y)
        R.Alt x y -> mkOr (expr x) (expr y)
        R.Eps -> LBool True
        R.Null -> LBool False
        STerm x -> x
        SNonterm (vs, nt') ->
          let vs' = M.findWithDefault [] nt' vars
          in mkAnd
               (copyVars vs (vs' & allFresh nt'))
               (M.findWithDefault (LBool True) nt' sols & allFresh nt')

collapse :: Map Int (Map NT (Set NT)) -> Map NT Expr -> Map NT Expr
collapse m sols' = M.unionsWith mkOr $ M.elems $ fmap collapseUnroll m
  where
    sols = fmap (vars . varName %~ head . splitOn "#") sols'
    collapseUnroll = fmap collapseSet
    collapseSet =
      manyAnd . map (\nt -> M.findWithDefault (LBool True) nt sols) . S.toList
