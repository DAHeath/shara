module Grammar.Graph2 where

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
  { graphForward :: Map Nonterminal [Rule]
  , graphBackward :: Map Nonterminal [Rule]
  } deriving (Show, Read, Eq, Ord)

data CloneInfo = CloneInfo 
  { copyToO :: (Map Nonterminal Nonterminal) 
  , oToCopy :: (Map Nonterminal [Nonterminal])
  } deriving (Show, Read, Eq, Ord)
type BackEdges = Set Rule

mkGraph :: Grammar -> Graph
mkGraph (Grammar _ rs) =
  let (fors, backs) = unzip $ map (\r@(Rule lhs _ rhs) ->
        ( M.fromList (zip rhs (repeat [r]))
        , M.singleton lhs [r]
        )) rs
  in Graph (M.unionsWith (++) fors) (M.unionsWith (++) backs)

forwardRules :: Nonterminal -> Graph -> [Rule]
forwardRules s = M.findWithDefault [] s . graphForward

backwardRules :: Nonterminal -> Graph -> [Rule]
backwardRules s = M.findWithDefault [] s . graphBackward

noterminals :: Graph -> Set Nonterminal
noterminals g = M.keysSet (graphForward g) `S.union` M.keysSet (graphBackward g)

initials :: Graph -> Set Nonterminal
initials g = S.filter (\s -> all (\r -> null (_ruleRHS r)) (backwardRules s g)) (noterminals g)

terminals :: Graph -> Set Nonterminal
terminals g = (noterminals g) `S.difference` (M.keysSet (graphForward g))

opens :: Graph -> Set Nonterminal
opens = initials

toGrammar :: Symbol -> Graph -> Grammar
toGrammar start gr =
  let rs = nub $ concat $ M.elems $ graphForward gr
  in Grammar start rs

plot :: FilePath -> Graph -> IO ()
plot fn = P.plot fn . toGrammar 0

plot2 :: FilePath -> Graph -> IO ()
plot2 fn = P.plot fn . toGrammar2 0

toGrammar2 :: Symbol -> Graph -> Grammar
toGrammar2 start gr =
  let rs = nub $ concat $ M.elems $ graphBackward gr
  in Grammar start rs

theNextId :: Graph -> Int
theNextId g = 
  let allSymbols = map (_nonterminalSymbol) (S.toList (terminals g))
    in findNextId 0 allSymbols
  where
    findNextId currentValue allSymbols = case allSymbols of
      [] -> currentValue
      x:xs -> if currentValue > x then findNextId currentValue xs
                 else findNextId (x+1) xs