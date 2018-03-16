{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.Disjoin2 where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Foldable

import           Formula hiding (Rule)

import           Grammar.Grammar

type DisSymbol = Symbol
type DisNonterm = Nonterminal

type Mapping = Map Symbol (Set DisNonterm)

mkDisjoint :: Grammar -> (Grammar, Mapping)
mkDisjoint = undefined

collapseSolution :: Mapping -> Map Symbol Expr -> Map Symbol Expr
collapseSolution = undefined

type SplitPoint = Set DisNonterm

data DisjoinState = DisjoinState
  { _localSplits :: Map Symbol (Set SplitPoint)
  , _parents :: Map Symbol (Set Symbol)
  , _parentSplits :: Map SplitPoint (Set SplitPoint)
  , _splitDependencies :: Map SplitPoint (Set DisNonterm)
  , _instances :: Map Symbol (Set DisNonterm)
  } deriving (Show, Read, Eq, Ord)
makeLenses ''DisjoinState

type Disjoin a = WriterT [Rule] (State DisjoinState) a

disjoinSym :: Grammar -> Symbol -> Disjoin ()
disjoinSym g s =
  let rs = rulesFor s (g ^. grammarRules)
  in undefined

dependencies :: Symbol -> Disjoin (Set DisNonterm)
dependencies s = do
  ss <- splitAncestry =<< (lookupSet s <$> use localSplits)
  unionsM (\s -> lookupSet s <$> use splitDependencies) ss

addDependency :: Symbol -> DisNonterm -> Disjoin ()
addDependency dependent dependency = do
  let dependencySym = view nonterminalSymbol dependency
  ds <- dependencies dependent
  ds' <- dependencies dependencySym
  let ds'' = S.insert dependency $ S.union ds ds'

  -- The dependent acquires the dependency as a parent.
  parents %= mapUnion dependent (S.singleton dependencySym)

  -- The dependency and its local ancestors gets the local splits of
  -- the dependent.
  locDep <- lookupSet dependent <$> use localSplits
  anc <- ancestry (S.singleton dependencySym)
  mapM_ (\a -> localSplits %= mapUnion a locDep) anc

  -- The dependent's local splits acquire the parents of the dependency's local
  -- splits.
  locDep' <- lookupSet dependencySym <$> use localSplits

  -- Push down all dependencies to the local splits of both
  -- propogate dependencies up to parents of the local splits
  -- lookupSet s
  undefined
  where
    propogateDeps :: Set DisNonterm -> Set SplitPoint -> Disjoin ()
    propogateDeps deps ss =
      undefined

ancestry :: Set Symbol -> Disjoin (Set Symbol)
ancestry ss = do
  ss' <- unionsM (\s -> lookupSet s <$> use parents) ss
  if ss' == ss then pure ss' else ancestry ss'

splitAncestry :: Set SplitPoint -> Disjoin (Set SplitPoint)
splitAncestry ss = do
  ss' <- unionsM (\s -> lookupSet s <$> use parentSplits) ss
  if ss' == ss then pure ss' else splitAncestry ss'

lookupSet :: Ord a => a -> Map a (Set b) -> Set b
lookupSet = M.findWithDefault S.empty

unionsM :: (Monad m, Foldable f, Ord b) => (a -> m (Set b)) -> f a -> m (Set b)
unionsM f = foldrM (\x acc -> S.union acc <$> f x) S.empty

mapUnion :: (Ord a, Ord b) => a -> Set b -> Map a (Set b) -> Map a (Set b)
mapUnion = M.insertWith S.union

-- | Given a dependent, choose the best possible dependency of the given
-- nonterminal. If there is no valid choice, then construct a new dependency.
-- Modify the dependencies of the dependent and dependency appropriately.
-- addDependency :: DisSymbol -> Nonterminal -> Disjoin DisNonterm
-- addDependency dependent dependency = do
