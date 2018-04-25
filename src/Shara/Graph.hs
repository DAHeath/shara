module Shara.Graph where

import           Data.Map      (Map)
import qualified Data.Map      as M
import           Data.Set      (Set)
import qualified Data.Set      as S
import           Shara.Grammar
import qualified Shara.Reg     as R

type Symbol = Int

data Graph = Graph
  { graphForward  :: Map Symbol [Symbol]
  , graphBackward :: Map Symbol [[Symbol]]
  } deriving (Show, Read, Eq, Ord)

successors :: Symbol -> Graph -> [Symbol]
successors s = M.findWithDefault [] s . graphForward

predecessors :: Symbol -> Graph -> [[Symbol]]
predecessors s = M.findWithDefault [] s . graphBackward

symbols :: Graph -> Set Symbol
symbols g = M.keysSet (graphForward g) `S.union` M.keysSet (graphBackward g)

initials :: Graph -> Set Symbol
initials g = S.filter (\s -> all null (predecessors s g)) (symbols g)

terminals :: Graph -> Set Symbol
terminals g = symbols g `S.difference` M.keysSet (graphForward g)

clear :: Set Symbol -> Graph -> Graph
clear toClear (Graph for back) = Graph for' back'
  where
    for' =
      M.filterWithKey (\k _ -> k `notElem` toClear) $
      fmap (filter (`notElem` toClear)) for
    back' =
      M.filterWithKey (\k _ -> k `notElem` toClear) $
      fmap (map (filter (`notElem` toClear))) back

grammarToGraph :: Grammar a -> Graph
grammarToGraph (SGrammar _ rs) = Graph forw back
  where
    back = fmap ruleSymbols rs
    forw = foldr addForw M.empty (M.toList back)
    addForw ::
         (Symbol, [[Symbol]]) -> Map Symbol [Symbol] -> Map Symbol [Symbol]
    addForw (snk, srcs) m =
      foldr (\src -> M.insertWith (++) src [snk]) m (concat srcs)
    ruleSymbols :: Rule a -> [[Symbol]]
    ruleSymbols =
      \case
        R.Null -> []
        R.Eps -> []
        R.Neg a -> ruleSymbols a
        R.Alt a b -> ruleSymbols a ++ ruleSymbols b
        R.Seq a b ->
          let as = ruleSymbols a
              bs = ruleSymbols b
          in if null as
               then bs
               else if null bs
                      then as
                      else [a' ++ b' | a' <- as, b' <- bs]
        Nonterm nt -> [[nt]]
        Term _ -> []
