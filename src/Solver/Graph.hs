module Solver.Graph where

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Grammar

type Symbol = Int

data Graph = Graph
  { graphForward :: Map Symbol [Symbol]
  , graphBackward :: Map Symbol [[Symbol]]
  } deriving (Show, Read, Eq, Ord)

successors :: Symbol -> Graph -> [Symbol]
successors s = M.findWithDefault [] s . graphForward

predecessors :: Symbol -> Graph -> [[Symbol]]
predecessors s = M.findWithDefault [] s . graphBackward

symbols :: Graph -> Set Symbol
symbols g = M.keysSet (graphForward g) `S.union` M.keysSet (graphBackward g)

initials :: Graph -> Set Symbol
initials g =
  S.filter (\s -> all null (predecessors s g)) (symbols g)

terminals :: Graph -> Set Symbol
terminals g = symbols g `S.difference` M.keysSet (graphForward g)

grammarToGraph :: Grammar a -> Graph
grammarToGraph (Grammar _ rs) = Graph forw back
  where
    back = M.mapKeys (\(NT nt) -> nt) (fmap ruleSymbols rs)
    forw = foldr addForw M.empty (M.toList back)

    addForw :: (Symbol, [[Symbol]]) -> Map Symbol [Symbol] -> Map Symbol [Symbol]
    addForw (snk, srcs) m = foldr (\src -> M.insertWith (++) src [snk]) m (concat srcs)

    ruleSymbols :: Rule a -> [[Symbol]]
    ruleSymbols = \case
      Null -> []
      Eps -> []
      Alt a b -> ruleSymbols a ++ ruleSymbols b
      Seq a b ->
        let as = ruleSymbols a
            bs = ruleSymbols b
        in if null as then bs else if null bs then as else [a' ++ b' | a' <- as, b' <- bs]
      Nonterminal (NT nt) -> [[nt]]
      Terminal _ -> []
