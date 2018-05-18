module Shara.Shara where

import           Control.Lens
import           Control.Monad.State
import           Data.IntMap                 (IntMap)
import qualified Data.IntMap                 as M
import           Data.IntSet                 (IntSet)
import qualified Data.IntSet                 as S
import           Data.Language.Grammar
import qualified Data.Language.Reg           as R
import qualified Data.Language.ScopedGrammar as SG
import           Data.List.Split             (splitOn)
import           Formula
import qualified Formula.Z3                  as Z3
import           Shara.CDD
import           Shara.Interpolate

data SolveKind
  = Topological
  | LicketySplit LicketySplitOptions
  deriving (Show, Read, Eq, Ord)

shara ::
     MonadIO m
  => SolveKind
  -> IntMap [Var]
  -> SG.Grammar [Var] Expr
  -> m (Either Model (IntMap Expr))
shara sk vocab sg = evalStateT (go =<< cdd sg) (emptyCDDState vocab)
  where
    go g =
      sharaStep sk g >>= \case
        Left m -> pure (Left m)
        Right m ->
          inductive vocab m sg >>= \case
            Nothing -> pure (Right m)
            Just _ -> go =<< unrollCDD g {- inds -}

-- | A Shara variant which does not check inductiveness and does not attempt to
-- unwind the grammar: Used for nontercursive problems.
sharaNonrecursive ::
     MonadIO m
  => SolveKind
  -> IntMap [Var]
  -> SG.Grammar [Var] Expr
  -> m (Either Model (IntMap Expr))
sharaNonrecursive sk vocab sg =
  evalStateT (sharaStep sk =<< cdd sg) (emptyCDDState vocab)

-- | Perform a single step -- solving a particular unwinding of the grammar.
sharaStep ::
     (MonadIO m, MonadState CDDState m)
  => SolveKind
  -> IGrammar m' Expr
  -> m (Either Model (IntMap Expr))
sharaStep sk g =
  solveDirect sk (finitePrefix g) >>= \case
    Left m -> pure (Left m)
    Right m -> do
      cs <- use clones
      pure (Right $ collapse cs m)

solveDirect ::
     MonadIO m => SolveKind -> Grammar Expr -> m (Either Model (IntMap Expr))
solveDirect =
  \case
    Topological -> topologicalInterpolation
    LicketySplit strat -> licketySplit strat

inductive ::
     MonadIO m
  => IntMap [Var]
  -> IntMap Expr
  -> SG.Grammar [Var] Expr
  -> m (Maybe IntSet)
inductive vs sols g = do
  s <- S.fromList . concat <$> M.traverseWithKey indRule (SG.rules g)
  pure $
    if S.null (SG.nonterminals g S.\\ s)
      then Nothing
      else Just s
  where
    indRule :: MonadIO m => NT -> SG.Rule [Var] Expr -> m [NT]
    indRule nt r =
      let conseq = M.findWithDefault (LBool False) nt sols
          ante = ex r
      in Z3.entails ante conseq >>= \case
           True -> pure [nt]
           False -> pure []
    ex =
      \case
        R.Seq x y -> mkAnd (ex x) (ex y)
        R.Alt x y -> mkOr (ex x) (ex y)
        R.Eps -> LBool True
        R.Null -> LBool False
        SG.Term x -> x
        SG.Nonterm vs' nt' ->
          let vs'' = M.findWithDefault [] nt' vs
          in mkAnd
               (copyVars vs' (vs'' & allFresh nt'))
               (M.findWithDefault (LBool True) nt' sols & allFresh nt')

collapse :: IntMap (IntMap IntSet) -> IntMap Expr -> IntMap Expr
collapse m sols' = M.unionsWith mkOr $ M.elems $ fmap collapseUnroll m
  where
    sols = fmap (vars . varName %~ head . splitOn "#") sols'
    collapseUnroll = fmap collapseSet
    collapseSet =
      manyAnd . map (\nt -> M.findWithDefault (LBool True) nt sols) . S.toList
