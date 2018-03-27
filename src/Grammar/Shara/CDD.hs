{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.TreeUnwind where

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
constructCDD :: Graph ->  (Graph,(Map Nonterminal Nonterminal))
constructCDD g = 
  let nonterminalList = topoplogicalSort g
      (UnwindState _ newGraph cloneInfo) = execState (splitNodes nonterminalList) (UnwindState 1 g M.empty)
    in (newGraph,cloneInfo)



topoplogicalSort :: Graph -> [Nonterminal]
topoplogicalSort g = 
  let startSet = initials g
   in sort [] (graphBackward g) startSet

sort  :: [Nonterminal] -> (Map Nonterminal [Rule]) -> Set Nonterminal ->  [Nonterminal]
sort oldList backwardRules startSet =
  if null startSet then oldList
  	else let nextList = S.toList startSet
  	         newBackwardRules = foldr M.delete backwardRules nextList
  	         newStartSet = undefined
  	        in sort (oldList++nextList) newBackwardRules newStartSet

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
  (UnwindState nextId (Graph graphForward graphBackward) cloneInfo) <- get
  let newGraph = (Graph (M.delete ns graphForward) (M.delete ns graphBackward) )
  put (UnwindState nextId newGraph cloneInfo)
  return ()

cloneNewNode :: Nonterminal -> Set Rule -> Unwind ()
cloneNewNode ns rules= do
  -- copy the nodes
  newNs  <- freshNonterminal ns
  (UnwindState nextId graph cloneInfo) <- get
  -- update clone info
  let newCloneInfo = M.insert newNs ns cloneInfo
  -- copy rules and update the graph
  let (Graph graphForward graphBackward) = graph
  let newRules = map (copyOldRule ns newNs) (S.toList rules)
  let newGraphForward = M.insert newNs newRules graphForward
  let newGraphBackward = M.insert newNs (backwardRules ns graph) graphBackward
  let newGraph = (Graph newGraphForward newGraphBackward)
  put (UnwindState nextId newGraph newCloneInfo)
  return ()

copyOldRule :: Nonterminal -> Nonterminal -> Rule -> Rule
copyOldRule oldNs newNs (Rule h expr bodys) = case (L.elemIndex oldNs bodys) of
  Just index -> let firstPart = take index bodys
                    secondPart = drop (index+1) bodys
                   in (Rule h expr (firstPart++[newNs]++secondPart))
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

isDisjoin :: (Nonterminal,Nonterminal) -> Unwind Bool
isDisjoin = undefined


freshNonterminal :: Nonterminal -> Unwind Nonterminal
freshNonterminal (Nonterminal _ vars) = do
	(UnwindState nextId graph cloneInfo) <- get
	put (UnwindState (nextId+1) graph cloneInfo)
	return (Nonterminal nextId vars)


