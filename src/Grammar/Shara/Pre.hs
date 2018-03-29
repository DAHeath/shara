{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.Pre where

import           Control.Monad.State

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L

import           Formula hiding (Rule)
import           Grammar.Grammar
import           Grammar.Graph2

data BackEdgeState = BackState
  { _node :: Set Nonterminal
   ,_backEdges :: Set Rule
   ,_removeGraph :: Graph
  } deriving (Show, Read, Eq, Ord)

type BackEdge a = State BackEdgeState a

-- unwind the graph that part is not enough
backEdges :: Graph -> (Set Rule)
backEdges g = 
  let startNodes =S.toList (terminals g)
      (BackState _ backEdges _) = execState (manyVisited S.empty startNodes) (BackState S.empty S.empty g)
    in backEdges


manyVisited :: (Set Nonterminal) -> [Nonterminal] -> BackEdge ()
manyVisited visitedNodes nodes = do
  mapM_ (isVisited visitedNodes) nodes
  return ()


isVisited :: (Set Nonterminal) -> Nonterminal -> BackEdge ()
isVisited visitedNodes n = do
  (BackState node _ _)  <- get
  if S.member n node then return ()
    else stepNode visitedNodes n

stepNode :: (Set Nonterminal) -> Nonterminal -> BackEdge ()
stepNode  visitedNodes n = do
 (BackState node backEdges g)  <- get
 let allEdges = backwardRules n g
 let (backRules,otherRules) =  L.partition (\r -> any (\n1 -> S.member n1 visitedNodes) (_ruleRHS r) ) allEdges
 let newBackEdges = foldr S.insert backEdges backRules 
 put (BackState (S.insert n node) newBackEdges g)
 manyVisited (S.insert n visitedNodes)  (concat (map _ruleRHS otherRules))
 return ()

