{-# LANGUAGE QuasiQuotes #-}
module Grammar.Shara where

import           Control.Monad.IO.Class

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Formula hiding (Rule)
import           Formula.Expr
import           Grammar.Grammar

import           Grammar.Graph2
import           Grammar.Shara.DAGUnwind
import           Grammar.Shara.Pre

solve :: Grammar ->IO (Maybe (Map Nonterminal Expr))
solve grammar@(Grammar symbol rules) = do
  let (oldMaps,noDuplicates) = copyDuplicates grammar
  let newGrammar = renameVariables noDuplicates
  let originalGraph = mkGraph newGrammar
  let removeSet = backEdges originalGraph
  let newRules = filter (\r -> S.notMember r removeSet) rules
  let firstUnwindDAG = mkGraph (Grammar symbol newRules)
  let allUseTerminas = terminals firstUnwindDAG
  let copyToO = foldr (\n m->M.insert n n m) M.empty allUseTerminas
  let oToCopy = foldr (\n m->M.insert n [n] m) M.empty allUseTerminas
  let cloneInfo = CloneInfo copyToO oToCopy
  solveReulst <- solveAux (S.toList removeSet) cloneInfo originalGraph firstUnwindDAG (theNextId originalGraph)
  case solveReulst of
    Nothing -> return Nothing
    Just solution -> return (Just (mapBackSolution oldMaps solution))


solveAux :: [Rule] -> CloneInfo -> Graph -> Graph -> Int -> IO (Maybe (Map Nonterminal Expr))
solveAux backEdges cloneInfo originalGraph currentDAG nextId = do
  solveReulst <- solveDAG currentDAG
  case solveReulst of
    Nothing -> return Nothing
    Just solution -> do let s = mergeSolution cloneInfo solution
                        maybeNextDAG <- (dagUnwind backEdges cloneInfo s originalGraph currentDAG nextId)
                        case maybeNextDAG of
                          Nothing -> return (Just s)
                          Just (UnwindResult ids newCloneInfo nextDAG) -> solveAux backEdges newCloneInfo originalGraph nextDAG ids

mergeSolution :: CloneInfo -> Map Nonterminal Expr -> Map Nonterminal Expr
mergeSolution (CloneInfo _ oToCopy) solutions = 
  let mapList = M.toList oToCopy
      newList = map (\(k,list) -> (k,getConjuntion solutions list)) mapList
    in M.fromList newList
  where
    getConjuntion solutions list = manyOr (map (\k -> solutions M.! k) list )

solveDAG :: Graph -> IO (Maybe (Map Nonterminal Expr))
solveDAG = undefined

mapBackSolution :: Map Nonterminal Nonterminal -> Map Nonterminal Expr -> Map Nonterminal Expr
mapBackSolution = undefined
