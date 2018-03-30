{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.DAGUnwind where

import           Control.Monad.State

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

import           Formula hiding (Rule)
import           Grammar.Grammar
import           Grammar.Graph2

data UnwindState = UnwindState
  { _nextId :: Int
  , _cloneInfo :: CloneInfo
  , _newNodes  :: Set Nonterminal
  , _graph :: Graph
  , _visitedRules :: Set Rule
  , _originalGraph :: Graph
  , _nextUnwindRules :: [Rule]
  } deriving (Show, Read, Eq, Ord)

data UnwindResult = UnwindResult
  { _nextId' :: Int
   ,_cloneInfo' :: CloneInfo
   ,_graph' :: Graph
  } deriving (Show, Read, Eq, Ord)

type Unwind a = State UnwindState a

-- unwind the graph that part is not enough
dagUnwind :: [Rule] ->  Int -> CloneInfo -> Map Nonterminal Expr -> Graph -> Graph -> IO (Maybe UnwindResult)
dagUnwind backEdges nextId cloneInfo solutions originalGraph lastUnwindDag = do
  notInductiveBackEdges' <- (mapM (removeInductiveEdge solutions) backEdges)
  let notInductiveBackEdges = concat notInductiveBackEdges'
  if null notInductiveBackEdges then return Nothing
    else do let (_,unwindResult) = runState unwindNewRules (UnwindState nextId cloneInfo (S.empty) lastUnwindDag (S.empty)  originalGraph notInductiveBackEdges)
            let (UnwindState nextId cloneInfo _ unwindDag _ _ _) = unwindResult
            return (Just (UnwindResult nextId cloneInfo unwindDag))


-- TODO : using solutions to decided if it needs to unwind
removeInductiveEdge :: Map Nonterminal Expr -> Rule ->IO [Rule]
removeInductiveEdge _ r =return [r]


unwindNewRules :: Unwind ()
unwindNewRules = do
  (UnwindState nextId cloneInfo newNodes graph visitedRules originalGraph nextUnwindRules) <- get
  if  null nextUnwindRules then return ()
    else do put (UnwindState nextId cloneInfo newNodes graph visitedRules originalGraph (tail nextUnwindRules))
            unwindNewRule (head nextUnwindRules)

unwindNewRule :: Rule -> Unwind ()
unwindNewRule rule = do
  (UnwindState nextId _ _ _ visitedRules _ _) <- get
  if S.member rule visitedRules then unwindNewRules
           else copyRule rule

copyRule :: Rule -> Unwind ()
copyRule r@(Rule h expr bodys) = do
  (UnwindState _ cloneInfo _ _ _ _ _) <- get
  let newH = head ((oToCopy cloneInfo) M.! h)
  newBodys <- mapM constructNewNode bodys
  let newRule = Rule newH expr newBodys
  (UnwindState nextId cloneInfo2 newNodes graph visitedRules originalGraph nextUnwindRules) <- get
  let (Graph forwardRules backwardRules) = graph
  let newForwardRules = updateRule newRule newH forwardRules
  let newBackwardRules = foldr (updateRule newRule) backwardRules newBodys
  let newVisitedRules = S.insert r visitedRules
  let newGraph = Graph newForwardRules newBackwardRules
  put (UnwindState nextId cloneInfo2 newNodes newGraph newVisitedRules originalGraph nextUnwindRules)
  unwindNewRules


updateRule :: Rule -> Nonterminal -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
updateRule r n partGraph = case (M.lookup n partGraph) of 
  Just list -> let newList = S.toList (S.insert r (S.fromList list))
                  in M.insert n newList partGraph
  Nothing -> M.insert n [r] partGraph

constructNewNode :: Nonterminal -> Unwind Nonterminal
constructNewNode n = do
  (UnwindState _ cloneInfo newNodes _ _ _ _) <- get
  currentNode <- getHeadNode n
  if S.member currentNode newNodes then return currentNode
    else copyNewNodes n

getHeadNode :: Nonterminal -> Unwind Nonterminal
getHeadNode n = do
  (UnwindState _ cloneInfo _ _ _ _ _) <- get
  let oToCopyMaps = oToCopy cloneInfo
  if M.member n oToCopyMaps then return (head (oToCopyMaps M.! n))
    else copyNewNodes n


copyNewNodes :: Nonterminal -> Unwind Nonterminal
copyNewNodes n = do
  newNode <- freshNode n
  (UnwindState nextId cloneInfo newNodes graph visitedRules originalGraph nextUnwindRules) <- get
  let backRules = backwardRules n originalGraph
  put (UnwindState nextId cloneInfo newNodes graph visitedRules originalGraph (nextUnwindRules++backRules))
  return newNode

freshNode :: Nonterminal -> Unwind Nonterminal
freshNode n@(Nonterminal _ vars) = do
  (UnwindState nextId cloneInfo newNodes graph visitedRules originalGraph nextUnwindRules) <- get
  let newNode = (Nonterminal nextId vars)
  let (CloneInfo copyToO oToCopy) = cloneInfo
  let newCopyToO = M.insert newNode n copyToO
  let newOToCopy = updateClone n newNode oToCopy
  let newCreateNodes = S.insert newNode newNodes
  put (UnwindState (nextId+1) (CloneInfo newCopyToO newOToCopy) newCreateNodes graph visitedRules originalGraph nextUnwindRules)
  return newNode

updateClone :: Nonterminal -> Nonterminal -> Map Nonterminal [Nonterminal] -> Map Nonterminal [Nonterminal]
updateClone n newNode oToCopy = case (M.lookup n oToCopy) of
  Just list -> M.insert n (newNode:list) oToCopy
  Nothing -> M.insert n ([newNode]) oToCopy
