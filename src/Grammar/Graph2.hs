module Grammar.Graph2 where

import           Control.Lens

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Grammar.Grammar

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
mkGraph = undefined

forwardRules :: Nonterminal -> Graph -> [Rule]
forwardRules s = M.findWithDefault [] s . graphForward

backwardRules :: Nonterminal -> Graph -> [Rule]
backwardRules s = M.findWithDefault [] s . graphBackward

initials :: Graph -> Set Nonterminal
initials g = undefined

terminals :: Graph -> Set Nonterminal
terminals g = undefined

opens :: Graph -> Set Nonterminal
opens g = undefined

