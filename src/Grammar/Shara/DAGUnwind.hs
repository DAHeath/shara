{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.TreeUnwind where

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
  } deriving (Show, Read, Eq, Ord)

data UnwindResult = UnwindResult
  { _nextId' :: Int
   ,_cloneInfo' :: CloneInfo
   ,_graph' :: Graph
  } deriving (Show, Read, Eq, Ord)

type Unwind a = State UnwindState a

-- unwind the graph that part is not enough
dagUnwind ::  MonadIO m => Int -> CloneInfo -> Map Nonterminal Expr -> Graph -> Graph -> m (Maybe UnwindResult)
dagUnwind nextId cloneInfo solutions originalGraph lastUnwindDag = do
  let openNs = opens lastUnwindDag
  let originalNodes = map (\x -> (copyToO cloneInfo) M.! x) (S.toList openNs)
  let backEdges = concat (map (\n -> backwardRules n originalGraph) originalNodes)
  notInductiveBackEdges' <- (mapM (removeInductiveEdge solutions) backEdges)
  let notInductiveBackEdges = concat notInductiveBackEdges'
  if null notInductiveBackEdges then return Nothing
    else let (_,unwindResult) = runState (unwindNewRules notInductiveBackEdges) (UnwindState nextId cloneInfo (S.empty) lastUnwindDag (S.empty)  originalGraph)
             (UnwindState nextId cloneInfo _ unwindDag _ _) = unwindResult
            in return (Just (UnwindResult nextId cloneInfo unwindDag))


-- TODO : using solutions to decided if it needs to unwind
removeInductiveEdge :: MonadIO m => Map Nonterminal Expr -> Rule ->m [Rule]
removeInductiveEdge _ r = [r]


unwindNewRules :: [Rule] -> Unwind ()
unwindNewRules rs = do
  mapM_ unwindNewRule rs
  return ()

unwindNewRule :: Rule -> Unwind ()
unwindNewRule rule = do
  (UnwindState _ _ _ _ visitedRules _) <- get
  if S.member rule visitedRules then return ()
    else copyRule rule

copyRule :: Rule -> Unwind ()
copyRule r@(Rule h expr bodys) = do
  (UnwindState _ cloneInfo _ _ _ _) <- get
  let newH = head ((oToCopy cloneInfo) M.! h)
  newBodys <- mapM constructNewNode bodys
  let newRule = Rule newH expr newBodys
  (UnwindState nextId cloneInfo2 newNodes graph visitedRules originalGraph) <- get
  let (Graph forwardRules backwardRules) = graph
  let newForwardRules = updateRule newRule newH forwardRules
  let newBackwardRules = foldr (updateRule newRule) backwardRules newBodys
  let newVisitedRules = S.insert r visitedRules
  let newGraph = Graph newForwardRules newBackwardRules
  put (UnwindState nextId cloneInfo2 newNodes newGraph newVisitedRules originalGraph)


updateRule :: Rule -> Nonterminal -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
updateRule r n partGraph = case (M.lookup n partGraph) of 
  Just list -> let newList = S.toList (S.insert r (S.fromList list))
                  in M.insert n newList partGraph
  Nothing -> M.singleton n [r] 

constructNewNode :: Nonterminal -> Unwind Nonterminal
constructNewNode n = do
  (UnwindState _ cloneInfo newNodes _ _ _) <- get
  let currentNode = head ((oToCopy cloneInfo) M.! n)
  if S.member currentNode newNodes then return currentNode
    else copyNewNodes n

copyNewNodes :: Nonterminal -> Unwind Nonterminal
copyNewNodes n = do
  newNode <- freshNode n
  (UnwindState _ _ _ _ _ originalGraph) <- get
  let backRules = backwardRules n originalGraph
  unwindNewRules backRules
  return newNode

freshNode :: Nonterminal -> Unwind Nonterminal
freshNode n@(Nonterminal _ vars) = do
  (UnwindState nextId cloneInfo newNodes graph visitedRules originalGraph) <- get
  let newNode = (Nonterminal nextId vars)
  let (CloneInfo copyToO oToCopy) = cloneInfo
  let newCopyToO = M.insert newNode n copyToO
  let newOToCopy = updateClone n newNode oToCopy
  put (UnwindState (nextId+1) (CloneInfo newCopyToO newOToCopy) newNodes graph visitedRules originalGraph)
  return newNode

updateClone :: Nonterminal -> Nonterminal -> Map Nonterminal [Nonterminal] -> Map Nonterminal [Nonterminal]
updateClone n newNode oToCopy = case (M.lookup n oToCopy) of
  Just list -> M.insert n (newNode:list) oToCopy
  Nothing -> M.insert n ([newNode]) oToCopy
