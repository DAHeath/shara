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
import           Grammar.Graph

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

-- Unwind the given CHC system to a tree. In addition, rename the variables in
-- the query to be consistent with the new CHC vocabulary and generate a map
-- from symbols in the original grammar to symbols in the new grammar.
treeUnwind :: Expr -> Grammar -> (Expr, Grammar, Map Symbol (Set Symbol))
treeUnwind q g =
  let start = g ^. grammarStart
      startNT = view ruleLHS $ head $ rulesFor start (g ^. grammarRules)
      finalState = execState (loop (mkGraph g) startNT) emptyState
      g' = Grammar 0 (view rules finalState)
      startNT' = view ruleLHS $ head $ rulesFor 0 (g' ^. grammarRules)
      (vMap, equivs) =
        mkMapping (zip (view nonterminalVars startNT) (view nonterminalVars startNT'))
  in (subst vMap q `mkAnd` equivs, g', view mapping finalState)

-- The core loop generates fresh nonterminals with uniquely named variables for
-- all rules for a particular vertex. It generates fresh rules using these new
-- nonterminals.
loop :: Graph -> Nonterminal -> Unwind Nonterminal
loop gr nt = do
  nt' <- freshNonterminal nt
  let s = view nonterminalSymbol nt
  mapping %= M.insertWith S.union s (S.singleton (view nonterminalSymbol nt'))
  mapM_ (handleRule nt') (backwardRules s gr)
  pure nt'
  where
    handleRule lhs' (Rule lhs phi rhs) = do
      rhs' <- mapM (loop gr) rhs
      let phi' = adjustFormula lhs lhs' rhs rhs' phi
      rules %= (Rule lhs' phi' rhs' :)

    -- There are two parts to rewriting formulas. First, we must replace
    -- variables by their fresh versions. Second, if a variable has more than one
    -- fresh version, we must set these duplicates equal to one another.
    adjustFormula lhs lhs' rhs rhs' phi =
      let origVars = concatMap (view nonterminalVars) (lhs:rhs)
          newVars = concatMap (view nonterminalVars) (lhs':rhs')
          (vMap, equivs) = mkMapping (zip origVars newVars)
      in
      subst vMap phi `mkAnd` equivs

mkMapping :: [(Var, Var)] -> (Map Var Var, Expr)
mkMapping = foldr adjust (M.empty, LBool True)

adjust :: (Var, Var) -> (Map Var Var, Expr) -> (Map Var Var, Expr)
adjust (v, v') (m, f) = case M.lookup v m of
  Nothing -> (M.insert v v' m, f)
  Just v'' -> (m, mkEql (view varType v') (V v') (V v'') `mkAnd` f)

freshNonterminal :: Nonterminal -> Unwind Nonterminal
freshNonterminal (Nonterminal _ vs) = do
  sym' <- symCounter <<+= 1
  vs' <- mapM freshVar vs
  pure (Nonterminal sym' vs')

freshVar :: Var -> Unwind Var
freshVar (Var _ t) = do
  vc <- varCounter <<+= 1
  let vn = "&" ++ show vc
  pure (Var vn t)
