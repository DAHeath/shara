{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.Pre where

import           Control.Monad.State

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L

import           Formula hiding (Rule)
import           Formula.Var
import           Formula.Expr
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

-- given a pre-processing grammar, do the first unwind
buildGraph :: Grammar -> (Graph,Graph)
buildGraph grammar@(Grammar symbol rules) = 
  let originalGraph = mkGraph grammar
      removeSet = backEdges originalGraph
      newRules = filter (\r -> S.notMember r removeSet) rules
      firstUnwindDAG = mkGraph (Grammar symbol newRules)
      allUseTerminas = terminals firstUnwindDAG
      copyToO = foldr (\n m->M.insert n n m) M.empty allUseTerminas
      oToCopy = foldr (\n m->M.insert n [n] m) M.empty allUseTerminas
      cloneInfo = CloneInfo copyToO oToCopy
    in (originalGraph,firstUnwindDAG)

data RenameState = RenameState
  { _extraConstrains :: [Expr]
    ,_Maps :: Map Var Var    
  } deriving (Show, Read, Eq, Ord)

type Rename a = State RenameState a
-- given a pre-processing grammar, rename the rules
renameVariables :: Grammar -> Grammar
renameVariables (Grammar symbol rules ) = (Grammar symbol (map renameRule rules))

renameRule :: Rule -> Rule
renameRule (Rule h expr body) = 
 let (newNs,renameState) = runState (renameNs (h:body)) (RenameState [] M.empty)
     newExpr = substitute (_Maps renameState) expr
     completeConstrains = manyAnd (newExpr:(_extraConstrains renameState))
    in (Rule (head newNs) completeConstrains (tail newNs))

renameNs :: [Nonterminal] -> Rename [Nonterminal]
renameNs = mapM renameN

renameN :: Nonterminal ->Rename Nonterminal
renameN (Nonterminal symbol vars) = do
  newVars <- mapM (renameVar symbol) (zip vars [1 ..])
  return (Nonterminal symbol newVars)

renameVar :: Int -> (Var,Int) ->Rename Var
renameVar symbol (v,index) = do
  (RenameState constrains oldMaps) <- get
  let (Var _ sort) = v
  let newVar = (Var ("arg"++show(index)++"#"++show(symbol)) sort)
  if M.member v oldMaps 
    then do let newEqual = mkEql sort (V newVar) (V (oldMaps M.! v))
            put (RenameState (newEqual:constrains) oldMaps)
    else do let newMaps = M.insert v newVar oldMaps
            put (RenameState constrains newMaps)
  return newVar

data SplitState = SplitState
  { _splitId :: Int
    ,_splitRules :: [Rule]
    ,_newToOldMap :: Map Nonterminal Nonterminal
  } deriving (Show, Read, Eq, Ord)

type Split a = State SplitState a

-- TODO, need to chanage 0 to the next Id
copyDuplicates :: Grammar -> (Map Nonterminal Nonterminal, Grammar)
copyDuplicates (Grammar symbol rules) = 
  let (SplitState _ newRules maps ) = execState (splitRules) (SplitState 0 rules M.empty)
     in (maps,(Grammar symbol newRules))


splitRules :: Split ()
splitRules = do
  (SplitState splitId rules newToOld) <- get
  case takeFirst isDuplicateRule rules of
    Nothing -> return ()
    Just r -> do let restRules = filter (/= r) rules
                 newRules <- splitRule r
                 put (SplitState splitId (rules++newRules) newToOld)
                 splitRules

 
takeFirst :: (Rule -> Bool) -> [Rule] -> Maybe Rule
takeFirst f list = case list of
  [] -> Nothing
  x:xs -> if f x then (Just x) else takeFirst f xs 

splitRule :: Rule -> Split [Rule]
splitRule (Rule h expr body) = do
  (newBodys, newToOld) <- splitDuplicate S.empty M.empty body
  (SplitState splitId rules newToOldMap) <- get
  let newRules = addNewRules rules newToOld 
  let newRule = (Rule h expr newBodys)
  put (SplitState splitId rules (M.union newToOldMap newToOld)) 
  return (newRule:newRules)

addNewRules :: [Rule] -> Map Nonterminal Nonterminal -> [Rule]
addNewRules oldRules newPairs = concat (map (addNewRule oldRules) (M.toList newPairs))

addNewRule :: [Rule] -> (Nonterminal,Nonterminal) -> [Rule]
addNewRule oldRules (new,old) = 
  let validRules = filter (\r -> (_ruleLHS r) == old ) oldRules
      newRules = map (\(Rule _ expr body) -> (Rule new expr body) ) validRules
    in validRules

splitDuplicate :: Set Nonterminal -> Map Nonterminal Nonterminal -> [Nonterminal] ->Split ([Nonterminal],Map Nonterminal Nonterminal)
splitDuplicate visitSet nToOldN list = case list of
  [] ->return  ([],nToOldN)
  x:xs -> if S.member x visitSet
             then do freshN <- copy x
                     let newNToOldN = M.insert freshN x nToOldN
                     (bodys,finalNToOldN) <- splitDuplicate (S.insert x visitSet) newNToOldN xs
                     return ((freshN:bodys),finalNToOldN)
            else do (bodys,finalNToOldN) <- splitDuplicate (S.insert x visitSet) nToOldN xs
                    return ((x:bodys),finalNToOldN)

copy :: Nonterminal -> Split Nonterminal
copy (Nonterminal _ vars) = do
  (SplitState nextId r m ) <- get
  put (SplitState (nextId+1) r m)
  return (Nonterminal nextId vars)

isDuplicateRule :: Rule -> Bool
isDuplicateRule (Rule _ _ body) = isDuplicate body

isDuplicate :: [Nonterminal] -> Bool
isDuplicate list = isDuplicateN S.empty list  
  where
    isDuplicateN visitSet list = case list of
      [] -> False
      x:xs -> if S.member x visitSet then True
                 else isDuplicateN (S.insert x visitSet) xs

