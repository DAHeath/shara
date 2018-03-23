{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.TreeUnwind where

import           Control.Lens hiding (mapping)
import           Control.Monad.State

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

import           Formula hiding (Rule)
import           Grammar.Grammar

data UnwindState = UnwindState
  { _varCounter :: Int
  , _symCounter :: Int
  , _rules :: [Rule]
  , _mapping :: Map Symbol (Set Symbol)
  } deriving (Show, Read, Eq, Ord)
makeLenses ''UnwindState

type Unwind a = State UnwindState a

emptyState :: UnwindState
emptyState = UnwindState
  { _varCounter = 0
  , _symCounter = 0
  , _rules = []
  , _mapping = M.empty
  }

treeUnwind :: Expr -> Grammar -> (Expr, Grammar, Map Symbol (Set Symbol))
treeUnwind q g =
  let start = g ^. grammarStart
      rs = g ^. grammarRules
      startNT = view ruleLHS $ head $ rulesFor start rs
      finalState = execState (loop rs startNT) emptyState
      g' = Grammar 0 (view rules finalState)
      startNT' = view ruleLHS $ head $ rulesFor 0 (g' ^. grammarRules)
      (vMap, equivs) =
        mkMapping (zip (view nonterminalVars startNT) (view nonterminalVars startNT'))
  in (subst vMap q `mkAnd` equivs, g', view mapping finalState)

loop :: [Rule] -> Nonterminal -> Unwind Nonterminal
loop rs nt =
  let s = view nonterminalSymbol nt
      rs' = rulesFor s rs
  in do
    nt' <- freshNonterminal nt
    mapM_ (handleRule nt') rs'
    pure nt'
  where
    handleRule lhs' (Rule lhs phi rhs) = do
      rhs' <- mapM (loop rs) rhs
      let phi' = adjustFormula lhs lhs' rhs rhs' phi
      rules %= (Rule lhs' phi' rhs' :)

    adjustFormula lhs lhs' rhs rhs' phi =
      let origVars = concatMap (view nonterminalVars) (lhs:rhs)
          newVars = concatMap (view nonterminalVars) (lhs':rhs')
          (mapping, equivs) = mkMapping (zip origVars newVars)
      in
      subst mapping phi `mkAnd` equivs

mkMapping :: [(Var, Var)] -> (Map Var Var, Expr)
mkMapping = foldr adjust (M.empty, LBool True)

adjust :: (Var, Var) -> (Map Var Var, Expr) -> (Map Var Var, Expr)
adjust (v, v') (m, f) = case M.lookup v m of
  Nothing -> (M.insert v v' m, f)
  Just v'' -> (m, mkEql (view varType v') (V v') (V v'') `mkAnd` f)

freshNonterminal :: Nonterminal -> Unwind Nonterminal
freshNonterminal (Nonterminal sym vs) = do
  sym' <- symCounter <<+= 1
  vs' <- mapM freshVar vs
  pure (Nonterminal sym' vs')

freshVar :: Var -> Unwind Var
freshVar (Var _ t) = do
  vc <- varCounter <<+= 1
  let vn = "&" ++ show vc
  pure (Var vn t)
