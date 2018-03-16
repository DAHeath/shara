{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.Disjoin where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Formula hiding (Rule)

import           Grammar.Grammar

type DisSymbol = Symbol
type DisNonterm = Nonterminal

type Mapping = Map Symbol (Set DisNonterm)

mkDisjoint :: Grammar -> (Grammar, Mapping)
mkDisjoint = undefined

collapseSolution :: Mapping -> Map Symbol Expr -> Map Symbol Expr
collapseSolution = undefined

data DisjoinState = DisjoinState
  -- For a particular vertex, what are the instances which have already been used?
  { _dependencies :: Map DisSymbol Mapping
  -- All instances which are currently available.
  , _available :: Mapping
  -- A counter used to construct new instances.
  , _counter :: Symbol
  } deriving (Show, Read, Eq, Ord)
makeLenses ''DisjoinState

type Disjoin a = WriterT [Rule] (State DisjoinState) a

disjoinSym :: Grammar -> Symbol -> Disjoin ()
disjoinSym g s =
  let rs = rulesFor s (g ^. grammarRules)
  in undefined

disjoinRule :: Grammar -> Rule -> Disjoin ()
disjoinRule = undefined

-- | Given a dependent, choose the best possible dependency of the given
-- nonterminal. If there is no valid choice, then construct a new dependency.
-- Modify the dependencies of the dependent and dependency appropriately.
addDependency :: DisSymbol -> Nonterminal -> Disjoin DisNonterm
addDependency dependent dependency = do
  let dependSym = view nonterminalSymbol dependency
  -- Find all of the possible instantiations of the dependency.
  allChoices <- M.findWithDefault S.empty dependSym <$> use available
  -- Find all of the dependent's current dependencies.
  depends <- use dependencies
  let currentDeps = M.findWithDefault M.empty dependent depends
  -- Find the current dependencies on the dependency we are trying to add.
  let currentDep = M.findWithDefault S.empty dependSym currentDeps
  -- Only those which we are not already dependent on are valid.
  let validChoices = allChoices S.\\ currentDep :: Set DisNonterm
  -- Look up the dependencies of the valid choices.
  let validDeps =
        S.map (\c -> (c, M.findWithDefault M.empty (view nonterminalSymbol c) depends))
        validChoices :: Set (DisNonterm, Mapping)
  -- We cannot select any version which conflicts with dependencies we already have.
  let nonconflicting = S.filter (noConflict currentDeps . snd) validDeps
  -- Make a choice of dependency.
  choice <-
    if null nonconflicting
    -- Suppose that there are no choices which are nonconflicting.
    -- Then our only choice is to generate a fresh dependency.
    then freshDependency dependency
    -- Otherwise, we can select from the dependencies that are already available.
    else
      -- TODO optimize this choice
      pure (fst $ S.findMin nonconflicting)
  -- Add all the dependencies of the dependent to the new dependency.
  dependencies %= M.insertWith M.union (view nonterminalSymbol choice) currentDeps
  -- Add the new dependency to the list of dependencies of the dependent.
  dependencies . ix dependent %= M.insertWith S.union dependSym (S.singleton choice)
  pure choice

-- | There is no conflict between two mappings if all of their entries have an
-- empty intersection.
noConflict :: Mapping -> Mapping -> Bool
noConflict m1 m2 =
  all null (M.intersectionWith S.intersection m1 m2)

freshDependency :: Nonterminal -> Disjoin DisNonterm
freshDependency nt = do
  c <- counter <+= 1
  let newNt = nt & nonterminalSymbol .~ c
  available %= M.insertWith S.union (view nonterminalSymbol nt) (S.singleton newNt)
  dependencies %= M.insert c M.empty
  pure newNt
