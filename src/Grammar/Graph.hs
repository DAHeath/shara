module Grammar.Graph where

import           Control.Lens

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Data.List (nub)

import           Grammar.Grammar
import qualified Grammar.Plot as P

-- | A more efficient representation of a chc grammar when traversing it as if
-- it were a graph.
data Graph = Graph
  { graphForward :: Map Symbol [Rule]
  , graphBackward :: Map Symbol [Rule]
  } deriving (Show, Read, Eq, Ord)

data CloneInfo = CloneInfo
  { copyToO :: Map Symbol Symbol
  , oToCopy :: Map Symbol [Symbol]
  } deriving (Show, Read, Eq, Ord)
type BackEdges = Set Rule

mkGraph :: Grammar -> Graph
mkGraph (Grammar _ rs) =
  let (fors, backs) = unzip $ map (\r@(Rule lhs _ rhs) ->
        ( M.fromList (zip (map (view nonterminalSymbol) rhs) (repeat [r]))
        , M.singleton (view nonterminalSymbol lhs) [r]
        )) rs
  in Graph (M.unionsWith (++) fors) (M.unionsWith (++) backs)

forwardRules :: Symbol -> Graph -> [Rule]
forwardRules s = M.findWithDefault [] s . graphForward

backwardRules :: Symbol -> Graph -> [Rule]
backwardRules s = M.findWithDefault [] s . graphBackward

successors :: Symbol -> Graph -> [Symbol]
successors s =
  map (view (ruleLHS . nonterminalSymbol)) . forwardRules s

predecessors :: Symbol -> Graph -> [[Symbol]]
predecessors s =
  map (toListOf (ruleRHS . traverse . nonterminalSymbol)) . backwardRules s

symbols :: Graph -> Set Symbol
symbols g = M.keysSet (graphForward g) `S.union` M.keysSet (graphBackward g)

initials :: Graph -> Set Symbol
initials g =
  S.filter (\s -> all (null . view ruleRHS) (backwardRules s g)) (symbols g)

terminals :: Graph -> Set Symbol
terminals g = symbols g `S.difference` M.keysSet (graphForward g)

restrict :: Set Symbol -> Graph -> Graph
restrict ss g =
  g { graphForward = restrictMap (graphForward g)
    , graphBackward = restrictMap (graphBackward g)
    }
  where
    restrictMap =
      M.filter (not . null) . M.map (filter allInSet) . M.filterWithKey keyInSet

    keyInSet :: Symbol -> [Rule] -> Bool
    keyInSet s _ = s `elem` ss

    allInSet :: Rule -> Bool
    allInSet (Rule lhs _ rhs) = all (`elem` ss) $ map (view nonterminalSymbol) (lhs : rhs)

edges :: Graph -> [([Symbol], Symbol)]
edges g =
  let rs = concat $ M.elems (graphBackward g)
  in map (\r -> (map (view nonterminalSymbol) (view ruleRHS r), view (ruleLHS . nonterminalSymbol) r)) rs

toGrammar :: Symbol -> Graph -> Grammar
toGrammar start gr =
  let rs = nub $ concat $ M.elems $ graphForward gr
  in Grammar start rs

toGrammar2 :: Symbol -> Graph -> Grammar
toGrammar2 start gr =
  let rs = nub $ concat $ M.elems $ graphBackward gr
  in Grammar start rs

plot :: FilePath -> Graph -> IO ()
plot fn = P.plot fn . toGrammar 0

plot2 :: FilePath -> Graph -> IO ()
plot2 fn = P.plot fn . toGrammar2 0

theNextId :: Graph -> Int
theNextId g = findNextId 0 (S.toList $ terminals g)
  where
    findNextId currentValue allSymbols = case allSymbols of
      [] -> currentValue
      x:xs -> if currentValue > x then findNextId currentValue xs
              else findNextId (x+1) xs
