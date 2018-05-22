{-# LANGUAGE QuasiQuotes #-}

module Shara.Chc where

import           Control.Lens                hiding (anon)
import           Control.Monad.State
import           Data.Foldable               (fold)
import           Data.Function               (on)
import           Data.IntMap                 (IntMap)
import qualified Data.IntMap                 as IM
import qualified Data.Language.Reg           as R
import qualified Data.Language.ScopedGrammar as SG
import           Data.List                   (nubBy)
import           Data.Map                    (Map)
import qualified Data.Map                    as M
import           Data.Set                    (Set)
import qualified Data.Set                    as S
import           Formula
import           Shara.Interpolate
import           Shara.Shara

chcStrategy ::
     Monad m
  => (IntMap [Var] -> SG.Grammar [Var] Expr -> m (Either a (IntMap Expr)))
  -> [Chc]
  -> m (Either a (Map Var Expr))
chcStrategy solver hcs =
  let (relToNt, ntToRel) = mapRels hcs
      (vs, mapBack) = varMapping relToNt hcs
      g = grammar relToNt vs hcs
   in solver vs g >>= \case
       Left m -> pure (Left m)
       Right m -> pure (Right (transcribe mapBack ntToRel m))

solveChc :: MonadIO m => [Chc] -> m (Either (Map Var Expr) (Map Var Expr))
solveChc = chcStrategy shara

solveNonrecursiveChc ::
     MonadIO m => [Chc] -> m (Either (Map Var Expr) (Map Var Expr))
solveNonrecursiveChc = chcStrategy sharaNonrecursive

mapRels :: [Chc] -> (Map Var Int, IntMap Var)
mapRels hcs =
  let allAs = foldMap apps hcs
  in foldMap mkMap (zip (S.toList allAs) [0 ..])
  where
    mkMap (v, n) = (M.singleton v n, IM.singleton n v)

varMapping :: Map Var Int -> [Chc] -> (IntMap [Var], Map String String)
varMapping rels hcs =
  let vs = nubBy (on (==) fst) (concatMap appVars hcs)
  in fold $ evalState (mapM mkMap vs) (0 :: Int)
  where
    mkMap (r, vs) = do
      let hd = M.findWithDefault 0 r rels
      vs' <- mapM anon vs
      let mapBack =
            M.fromList $
            zip (map (view varName) vs') (map (\n -> "!" ++ show n) [0 ..])
      pure (IM.singleton hd vs', mapBack)
    anon (Var _ t) = do
      s <- get
      put (s + 1)
      pure (Var ("!" ++ show s) t)

grammar :: Map Var Int -> IntMap [Var] -> [Chc] -> SG.Grammar [Var] Expr
grammar relToNt vMap = foldr (SG.alt . clause) SG.null
  where
    clause =
      \case
        Rule body form (App hd vs) ->
          let hd' = M.findWithDefault 0 hd relToNt
              vs' = IM.findWithDefault [] hd' vMap
              tbl = M.fromList (zip vs vs')
          in SG.Grammar
               R.Null
               (IM.singleton
                  hd'
                  (foldr
                     (R.seq . app)
                     (SG.Term $ form & subst tbl)
                     (body & subst tbl)))
        Query body form hd ->
          SG.Grammar
            (foldr (R.seq . app) (SG.Term (mkNot hd `mkAnd` form)) body)
            IM.empty
    app (App rel vs) = SG.Nonterm vs (M.findWithDefault 0 rel relToNt)

transcribe :: Map String String -> IntMap Var -> IntMap Expr -> Map Var Expr
transcribe mapBack ntToRel sol =
  (M.mapKeys (\k -> IM.findWithDefault (error "bad key") k ntToRel) $
   M.fromList (IM.toList sol)) &
  vars .
  varName %~
  lookupName mapBack
  where
    lookupName m k = M.findWithDefault k k m

apps :: Chc -> Set Var
apps =
  \case
    Rule body _ hd -> S.unions (rApp hd : map rApp body)
    Query body _ _ -> S.unions (map rApp body)
  where
    rApp (App a _) = S.singleton a

appVars :: Chc -> [(Var, [Var])]
appVars =
  \case
    Rule body _ hd -> map rApp (hd : body)
    Query body _ _ -> map rApp body
  where
    rApp (App a vs) = (a, vs)
