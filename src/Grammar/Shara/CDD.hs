{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.CDD where

import           Control.Monad.State

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L

import           Formula hiding (Rule)
import           Grammar.Grammar
import           Grammar.Graph2


data UnwindState = UnwindState
  {   nextId :: Int
    , graph :: Graph
    -- map from new nonterminal to old nonterminal
    , cloneInfo :: Map Nonterminal Nonterminal
  } deriving (Show, Read, Eq, Ord)

type Unwind a = State UnwindState a

-- given a recursion-free chc system, construct an equivalence
-- CDD chc system
constructCDD :: Int -> Graph ->  (Graph,(Map Nonterminal Nonterminal))
constructCDD nextId g = 
  let nonterminalList = toplogicalSort g
      (UnwindState _ newGraph cloneInfo) = execState (splitNodes nonterminalList) (UnwindState nextId g M.empty)
    in (newGraph,cloneInfo)



toplogicalSort :: Graph -> [Nonterminal]
toplogicalSort g = 
  let startSet = terminals g
      allNs = noterminals g
      newList = sort [] g startSet
      tailList =S.toList (S.difference allNs (S.fromList newList))
    in newList ++ tailList

sort  :: [Nonterminal] -> Graph -> Set Nonterminal ->  [Nonterminal]
sort oldList g startSet =
  if null startSet then oldList
    else let nextList = S.toList startSet
             newForwardRules = updateForwardRules g nextList
             newBackwardRules = foldr M.delete (graphBackward g) nextList
             newGraph = Graph newForwardRules newBackwardRules
             newStartSet = terminals newGraph
  	        in sort (oldList++nextList) newGraph newStartSet

updateForwardRules :: Graph -> [Nonterminal] -> Map Nonterminal [Rule]
updateForwardRules g removeNs = 
  let influenceNs = S.fromList (concat (map _ruleRHS (concat (map (\n -> backwardRules n g) removeNs))))
   in foldr (removeForward (S.fromList removeNs) ) (graphForward g) influenceNs

removeForward :: Set Nonterminal -> Nonterminal -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
removeForward removeNs theNode oldForward =
  let oldList = M.findWithDefault [] theNode oldForward
      newRuleList = filter (\r -> S.notMember (_ruleLHS r) removeNs) oldList
    in if null newRuleList then M.delete theNode oldForward
      else M.insert theNode newRuleList oldForward

splitNodes :: [Nonterminal] -> Unwind()
splitNodes nodes = do
	mapM_ splitNode nodes
	return ()

splitNode :: Nonterminal -> Unwind ()
splitNode ns = do
  (UnwindState _ graph _ ) <- get
  colorSet <- color ns
  -- clone new node and updates the graph with new rules
  mapM_ (cloneNewNode ns) (S.toList colorSet)
  -- remove the old node in the graph
  (UnwindState nextId g@(Graph graphForward graphBackward) cloneInfo) <- get
  let newFor1 = foldr deleteForward graphForward (backwardRules ns g)
  let newBack1  = foldr deleteBackward graphBackward (forwardRules ns g)
  let newFor2 = foldr deleteOtherForward newFor1 (forwardRules ns g)
  let newGraph = (Graph newFor2 (M.delete ns newBack1) )
  if null colorSet then put (UnwindState nextId g cloneInfo)
    else put (UnwindState nextId newGraph cloneInfo)
  return ()

deleteBackward :: Rule -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
deleteForward r@(Rule _ _ body) oldBackward = foldr (remove r) oldBackward body

deleteForward :: Rule -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
deleteBackward r@(Rule h _ _) oldForward = remove r h oldForward 

deleteOtherForward :: Rule -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
deleteOtherForward r@(Rule _ _ body) oldForward = foldr (remove r) oldForward body

remove :: Rule -> Nonterminal -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
remove r ns oldMap = case M.lookup ns oldMap of
  Just list -> let newList = filter (\n -> n /= r ) list
                in M.insert ns newList oldMap
  Nothing -> error "it is wrong, it should be here" 

cloneNewNode :: Nonterminal -> Set Rule -> Unwind ()
cloneNewNode ns rules= do
  -- copy the nodes
  newNs  <- freshNonterminal ns
  (UnwindState _ _ cloneInfo) <- get
  -- update clone info
  let newCloneInfo = M.insert newNs ns cloneInfo
  -- copy rules and update the graph
  newForwardRules <-  mapM (copyOldRule ns newNs) (S.toList rules)
  (UnwindState nextId graph _) <- get
  let (Graph graphForward graphBackward) = graph
  -- updates the graph for this node
  let newGraphForward1 = M.insert newNs newForwardRules graphForward
  let newBackwardRules = map (\(Rule _ expr body) -> (Rule newNs expr body) ) (backwardRules ns graph)
  let newGraphBackward1 = M.insert newNs newBackwardRules graphBackward
  -- update the graph for nodes be influenced
  let newGraphBackward2 = foldr insertBackward newGraphBackward1 newForwardRules
  let newGraphForward2 = foldr insertForward newGraphForward1 newBackwardRules
  let newGraph = (Graph newGraphForward2 newGraphBackward2)
  put (UnwindState nextId newGraph newCloneInfo)
  return ()

insertForward :: Rule -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
insertForward r@(Rule _ _ body) oldForward = foldr (insert r) oldForward body 

insertBackward :: Rule -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
insertBackward r@(Rule h _ _) oldBackward = insert r h oldBackward

insert :: Rule -> Nonterminal -> Map Nonterminal [Rule] -> Map Nonterminal [Rule]
insert r n oldSet = case M.lookup n oldSet of
  Just list -> M.insert n (r:list) oldSet
  Nothing -> error "it should have key"

copyOldRule :: Nonterminal -> Nonterminal -> Rule ->Unwind Rule
copyOldRule oldNs newNs (Rule h expr bodys) = case (L.elemIndex oldNs bodys) of
  Just index -> do let firstPart = take index bodys
                   let  secondPart = drop (index+1) bodys
                   let newRule = (Rule h expr (firstPart++[newNs]++secondPart))
                   (UnwindState nextId graph cloneInfo) <- get
                   let newForward = foldr (insert newRule) (graphForward graph) (firstPart++secondPart)
                   put (UnwindState nextId (Graph newForward (graphBackward graph)) cloneInfo)
                   return newRule
  Nothing -> error "it should show in this rule body"


color :: Nonterminal -> Unwind (Set (Set Rule))
color ns = do
  (UnwindState _ graph _) <- get
  let rules = forwardRules ns graph
  colorRules rules

colorRules :: [Rule] -> Unwind (Set (Set Rule))
colorRules [] = return S.empty
colorRules (x:xs) = do
  coloredRules <- colorRules xs
  colorRule x coloredRules 

colorRule :: Rule -> (Set (Set Rule)) -> Unwind (Set (Set Rule))
colorRule r coloredRules = do
  let listRules = (S.toList coloredRules)
  index <- satisifyIndex r listRules
  if index >= length listRules then return (S.fromList ((S.singleton r):listRules))
  	else let (firstPart,secondPart) = L.splitAt index listRules
  	         joinSet = head secondPart
  	         newSecondPart = tail secondPart
  	         in return (S.fromList (firstPart++[S.insert r joinSet]++newSecondPart))

satisifyIndex :: Rule -> [Set Rule] ->Unwind Int
satisifyIndex r coloredRules = satisifyIndexRec 0 r coloredRules
  where
     satisifyIndexRec index r coloredRules = case coloredRules of
     	[] -> return index
     	x:xs -> do
     	          satisify <- satisify r (S.toList x)
     	          if satisify then return index
     		        else satisifyIndexRec (index+1) r xs

     satisify r ruleSet = case ruleSet of
    	[] -> return True
    	x:xs -> do
    		      disjoin <- isDisjoin (_ruleLHS r,_ruleLHS x)
    		      if disjoin then satisify r xs
    		      	else return False

--TODO: this need rework to have a more efficient implementation
isDisjoin :: (Nonterminal,Nonterminal) -> Unwind Bool
isDisjoin (n1,n2) = do
  joinSet <- collectJoinSet n1
  return (S.notMember n2 joinSet)

-- given a nontermianl, collects it corresponding join set
collectJoinSet :: Nonterminal -> Unwind (Set Nonterminal)
collectJoinSet ns = do
  (UnwindState _ graph _) <- get
  let rules = forwardRules ns graph
  let nextNonterminas = foldr (\r s -> S.insert (_ruleLHS r) s) S.empty rules
  furtherJoinSets <- mapM collectJoinSet (S.toList nextNonterminas)
  let disjointNs = foldr (\r s -> S.union (S.fromList (filter (\n -> ns /= n) (_ruleRHS r))) s) S.empty rules
  joinSets <- mapM colllectBack (S.toList disjointNs)
  return (S.unions (furtherJoinSets++joinSets))

-- given a nontermianl, collects its back track nonterminals include itself
colllectBack :: Nonterminal -> Unwind (Set Nonterminal)
colllectBack ns = do
  (UnwindState _ graph _) <- get
  let rules = backwardRules ns graph
  let backNonterminals =S.toList (S.fromList (concat (map _ruleRHS rules)))
  allBackSet <- mapM colllectBack backNonterminals
  return (S.insert ns (S.unions allBackSet))



freshNonterminal :: Nonterminal -> Unwind Nonterminal
freshNonterminal (Nonterminal _ vars) = do
	(UnwindState nextId graph cloneInfo) <- get
	put (UnwindState (nextId+1) graph cloneInfo)
	return (Nonterminal nextId vars)


