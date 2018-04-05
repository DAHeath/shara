module Grammar.Shara.CDD where

import           Control.Lens
import           Control.Monad.State

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L

import           Formula hiding (Rule)
import           Grammar.Grammar
import           Grammar.Graph


data UnwindState = UnwindState
  {   nextId :: Int
    , graph :: Graph
    -- map from new nonterminal to old nonterminal
    , cloneInfo :: Map Symbol Symbol
  } deriving (Show, Read, Eq, Ord)

type Unwind a = State UnwindState a

-- given a recursion-free chc system, construct an equivalence
-- CDD chc system
constructCDD :: Int -> Graph -> (Graph, Map Symbol Symbol)
constructCDD nextId g =
  let nonterminalList = toplogicalSort g
      UnwindState _ newGraph cloneInfo = execState (splitNodes nonterminalList) (UnwindState nextId g M.empty)
  in (newGraph,cloneInfo)

toplogicalSort :: Graph -> [Symbol]
toplogicalSort g =
  let startSet = terminals g
      allNs = symbols g
      newList = sort [] g startSet
      tailList = S.toList (S.difference allNs (S.fromList newList))
    in newList ++ tailList

sort :: [Symbol] -> Graph -> Set Symbol -> [Symbol]
sort oldList g startSet =
  if null startSet then oldList
  else
    let nextList = S.toList startSet
        newForwardRules = updateForwardRules g nextList
        newBackwardRules = foldr M.delete (graphBackward g) nextList
        newGraph = Graph newForwardRules newBackwardRules
        newStartSet = terminals newGraph
    in sort (oldList++nextList) newGraph newStartSet

updateForwardRules :: Graph -> [Symbol] -> Map Symbol [Rule]
updateForwardRules g removeNs =
  let influenceNs = S.fromList (concatMap (toListOf (ruleRHS . traverse . nonterminalSymbol))
        (concatMap (`backwardRules` g) removeNs))
  in foldr (removeForward (S.fromList removeNs)) (graphForward g) influenceNs

removeForward :: Set Symbol -> Symbol -> Map Symbol [Rule] -> Map Symbol [Rule]
removeForward removeNs theNode oldForward =
  let oldList = M.findWithDefault [] theNode oldForward
      newRuleList = filter (\r -> view (ruleLHS . nonterminalSymbol) r `S.notMember` removeNs) oldList
  in if null newRuleList then M.delete theNode oldForward
     else M.insert theNode newRuleList oldForward

splitNodes :: [Symbol] -> Unwind()
splitNodes = mapM_ splitNode

splitNode :: Symbol -> Unwind ()
splitNode ns = do
  UnwindState _ (Graph _ back) _ <- get
  let nt = case M.lookup ns back of
        Nothing -> Nonterminal ns []
        Just (r:_) -> view ruleLHS r
  colorSet <- color ns
  -- clone new node and updates the graph with new rules
  mapM_ (cloneNewNode nt) (S.toList colorSet)
  -- remove the old node in the graph
  UnwindState nextId g@(Graph graphForward graphBackward) cloneInfo <- get
  let newFor1 = foldr deleteForward graphForward (backwardRules ns g)
  let newBack1  = foldr deleteBackward graphBackward (forwardRules ns g)
  let newFor2 = foldr deleteOtherForward newFor1 (forwardRules ns g)
  let newGraph = Graph newFor2 (M.delete ns newBack1)
  if null colorSet
  then put (UnwindState nextId g cloneInfo)
  else put (UnwindState nextId newGraph cloneInfo)
  return ()

deleteBackward :: Rule -> Map Symbol [Rule] -> Map Symbol [Rule]
deleteForward r@(Rule _ _ body) oldBackward = foldr (remove r . view nonterminalSymbol) oldBackward body

deleteForward :: Rule -> Map Symbol [Rule] -> Map Symbol [Rule]
deleteBackward r@(Rule h _ _) = remove r (view nonterminalSymbol h)

deleteOtherForward :: Rule -> Map Symbol [Rule] -> Map Symbol [Rule]
deleteOtherForward r@(Rule _ _ body) oldForward = foldr (remove r . view nonterminalSymbol) oldForward body

remove :: Rule -> Symbol -> Map Symbol [Rule] -> Map Symbol [Rule]
remove r ns oldMap = case M.lookup ns oldMap of
  Just list -> let newList = filter (/= r) list
               in M.insert ns newList oldMap
  Nothing -> error "it is wrong, it should be here" 

cloneNewNode :: Nonterminal -> Set Rule -> Unwind ()
cloneNewNode nt rules = do
  -- copy the nodes
  newNt  <- freshNonterminal nt
  let ns = view nonterminalSymbol nt
  let newNs = view nonterminalSymbol newNt
  UnwindState _ _ cloneInfo <- get
  -- update clone info
  let newCloneInfo = M.insert newNs ns cloneInfo
  -- copy rules and update the graph
  newForwardRules <- mapM (copyOldRule ns newNt) (S.toList rules)
  UnwindState nextId graph _ <- get
  let (Graph graphForward graphBackward) = graph
  -- updates the graph for this node
  let newGraphForward1 = M.insert newNs newForwardRules graphForward
  let newBackwardRules = map (ruleLHS .~ newNt) (backwardRules ns graph)
  let newGraphBackward1 = M.insert newNs newBackwardRules graphBackward
  -- update the graph for nodes be influenced
  let newGraphBackward2 = foldr insertBackward newGraphBackward1 newForwardRules
  let newGraphForward2 = foldr insertForward newGraphForward1 newBackwardRules
  let newGraph = Graph newGraphForward2 newGraphBackward2
  put (UnwindState nextId newGraph newCloneInfo)

insertForward :: Rule -> Map Symbol [Rule] -> Map Symbol [Rule]
insertForward r@(Rule _ _ body) oldForward = foldr (insert r . view nonterminalSymbol) oldForward body 

insertBackward :: Rule -> Map Symbol [Rule] -> Map Symbol [Rule]
insertBackward r@(Rule h _ _) = insert r (view nonterminalSymbol h)

insert :: Rule -> Symbol -> Map Symbol [Rule] -> Map Symbol [Rule]
insert r n oldSet = case M.lookup n oldSet of
  Just list -> M.insert n (r:list) oldSet
  Nothing -> error "it should have key"

copyOldRule :: Symbol -> Nonterminal -> Rule -> Unwind Rule
copyOldRule oldNs newNonterm (Rule h expr bodies) = case L.elemIndex oldNs (map (view nonterminalSymbol) bodies) of
  Just index -> do
    let firstPart = take index bodies
    let secondPart = drop (index+1) bodies
    let newRule = Rule h expr (firstPart ++ [newNonterm] ++ secondPart)
    UnwindState nextId graph cloneInfo <- get
    let newForward = foldr (insert newRule . view nonterminalSymbol) (graphForward graph) (firstPart ++ secondPart)
    put (UnwindState nextId (Graph newForward (graphBackward graph)) cloneInfo)
    return newRule
  Nothing -> error "it should show in this rule body"


color :: Symbol -> Unwind (Set (Set Rule))
color ns = do
  (UnwindState _ graph _) <- get
  let rules = forwardRules ns graph
  colorRules rules

colorRules :: [Rule] -> Unwind (Set (Set Rule))
colorRules [] = return S.empty
colorRules (x:xs) = do
  coloredRules <- colorRules xs
  colorRule x coloredRules 

colorRule :: Rule -> Set (Set Rule) -> Unwind (Set (Set Rule))
colorRule r coloredRules = do
  let listRules = S.toList coloredRules
  index <- satisfyIndex r listRules
  if index >= length listRules
  then return (S.fromList (S.singleton r:listRules))
  else let (firstPart,secondPart) = L.splitAt index listRules
           joinSet = head secondPart
           newSecondPart = tail secondPart
           in return (S.fromList (firstPart++[S.insert r joinSet]++newSecondPart))

satisfyIndex :: Rule -> [Set Rule] ->Unwind Int
satisfyIndex = satisfyIndexRec 0
  where
    satisfyIndexRec index r coloredRules = case coloredRules of
      [] -> return index
      x:xs -> do
        satisfy <- satisfy r (S.toList x)
        if satisfy then return index
        else satisfyIndexRec (index+1) r xs

    satisfy r ruleSet = case ruleSet of
      [] -> return True
      x:xs -> do
        disjoint <- areDisjoint (view (ruleLHS . nonterminalSymbol) r)
                                (view (ruleLHS . nonterminalSymbol) x)
        if disjoint then satisfy r xs
        else return False

--TODO: this need rework to have a more efficient implementation
areDisjoint :: Symbol -> Symbol -> Unwind Bool
areDisjoint n1 n2 = do
  joinSet <- collectJoinSet n1
  return (S.notMember n2 joinSet)

-- given a nontermianl, collects it corresponding join set
collectJoinSet :: Symbol -> Unwind (Set Symbol)
collectJoinSet ns = do
  (UnwindState _ graph _) <- get
  let rules = forwardRules ns graph
  let nextNonterminals = foldr (\r s -> S.insert (view (ruleLHS . nonterminalSymbol) r) s) S.empty rules
  furtherJoinSets <- mapM collectJoinSet (S.toList nextNonterminals)
  let disjointNs = foldr (\r s -> S.union (S.fromList (filter (/= ns) (toListOf (ruleRHS . traverse . nonterminalSymbol) r))) s) S.empty rules
  joinSets <- mapM collectBack (S.toList disjointNs)
  return (S.unions (furtherJoinSets++joinSets))

-- given a nontermianl, collects its back track nonterminals include itself
collectBack :: Symbol -> Unwind (Set Symbol)
collectBack ns = do
  (UnwindState _ graph _) <- get
  let rules = backwardRules ns graph
  let backNonterminals = L.nub $ map (view nonterminalSymbol) $ concatMap (view ruleRHS) rules
  allBackSet <- mapM collectBack backNonterminals
  return (S.insert ns (S.unions allBackSet))



freshNonterminal :: Nonterminal -> Unwind Nonterminal
freshNonterminal (Nonterminal _ vars) = do
  (UnwindState nextId graph cloneInfo) <- get
  put (UnwindState (nextId+1) graph cloneInfo)
  return (Nonterminal nextId vars)


