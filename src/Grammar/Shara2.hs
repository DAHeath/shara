module Grammar.Shara where

import           Control.Monad.IO.Class
import           Control.Arrow (second)

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Formula hiding (Rule)
import           Formula.Expr
import           Grammar.Grammar

import           Grammar.Graph
import           Grammar.Shara.DAGUnwind
import           Grammar.Shara.Pre

solve :: Expr -> Grammar -> IO (Maybe (Map Nonterminal Expr))
solve q grammar@(Grammar symbol rules) =
  let (oldMaps,noDuplicates) = copyDuplicates grammar
      newGrammar = renameVariables noDuplicates
      originalGraph = mkGraph newGrammar
      removeSet = backEdges originalGraph
      newRules = filter (`S.notMember` removeSet) rules
      firstUnwindDAG = mkGraph (Grammar symbol newRules)
      allUseTerminals = terminals firstUnwindDAG
      copyToO = foldr (\n m -> M.insert n n m) M.empty allUseTerminals
      oToCopy = foldr (\n m -> M.insert n [n] m) M.empty allUseTerminals
      cloneInfo = CloneInfo copyToO oToCopy
  in do
    solveReulst <- solveAux q (S.toList removeSet) cloneInfo originalGraph firstUnwindDAG (theNextId originalGraph)
    case solveReulst of
      Nothing -> return Nothing
      Just solution -> return (Just (mapBackSolution oldMaps solution))

solveAux :: Expr -> [Rule] -> CloneInfo -> Graph -> Graph -> Int -> IO (Maybe (Map Nonterminal Expr))
solveAux q backEdges cloneInfo originalGraph currentDAG nextId = do
  solveReulst <- solveDAG q currentDAG nextId
  case solveReulst of
    Nothing -> return Nothing
    Just solution -> do
      let s = mergeSolution cloneInfo solution
      maybeNextDAG <- dagUnwind backEdges cloneInfo s originalGraph currentDAG nextId
      case maybeNextDAG of
        Nothing -> return (Just s)
        Just (UnwindResult ids newCloneInfo nextDAG) -> solveAux q backEdges newCloneInfo originalGraph nextDAG ids

mergeSolution :: CloneInfo -> Map Nonterminal Expr -> Map Nonterminal Expr
mergeSolution (CloneInfo _ oToCopy) solutions = 
  let mapList = M.toList oToCopy
      newList = map (second (conjoin solutions)) mapList
    in M.fromList newList
  where
    conjoin solutions list = manyOr (map (\k -> solutions M.! k) list )

solveDAG :: Expr -> Graph -> Int -> IO (Maybe (Map Nonterminal Expr))
solveDAG = undefined

mapBackSolution :: Map Nonterminal Nonterminal -> Map Nonterminal Expr -> Map Nonterminal Expr
mapBackSolution = undefined
