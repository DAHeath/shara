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

solve :: Expr -> Grammar -> IO (Maybe (Map Symbol Expr))
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
  in solveAux q (S.toList removeSet) 
    cloneInfo originalGraph firstUnwindDAG (theNextId originalGraph) >>= \case
      Nothing -> return Nothing
      Just solution -> return (Just (mapBackSolution oldMaps solution))

solveAux :: Expr -> [Rule] -> CloneInfo -> Graph -> Graph -> Int -> IO (Maybe (Map Symbol Expr))
solveAux q backEdges cloneInfo originalGraph currentDAG nextId =
  solveDAG q currentDAG nextId >>= \case
    Nothing -> return Nothing
    Just solution -> do
      let s = mergeSolution cloneInfo solution
      maybeNextDAG <- dagUnwind backEdges cloneInfo s originalGraph currentDAG nextId
      case maybeNextDAG of
        Nothing -> return (Just s)
        Just (UnwindResult ids newCloneInfo nextDAG) -> solveAux q backEdges newCloneInfo originalGraph nextDAG ids

mergeSolution :: CloneInfo -> Map Symbol Expr -> Map Symbol Expr
mergeSolution (CloneInfo _ oToCopy) solutions =
  let mapList = M.toList oToCopy
      newList = map (second (conjoin solutions)) mapList
    in M.fromList newList
  where
    conjoin solutions list = manyOr (map (\k -> solutions M.! k) list )

solveDAG :: Expr -> Graph -> Int -> IO (Maybe (Map Symbol Expr))
solveDAG = undefined

mapBackSolution :: Map Symbol Symbol -> Map Symbol Expr -> Map Symbol Expr
mapBackSolution aliases =
  M.foldrWithKey (\k e -> M.insertWith mkOr (M.findWithDefault k k aliases) e) M.empty
