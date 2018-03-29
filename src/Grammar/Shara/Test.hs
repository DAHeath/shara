{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.Test where

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

import           Formula hiding (Rule)
import           Formula.Expr
import           Grammar.Grammar
import           Grammar.Graph2
import           Grammar.Shara.CDD
import           Grammar.Shara.DAGUnwind
import           Grammar.Shara.Pre

data Vertex = Vertex Int [Var] [Edge]

data Edge = Edge [Vertex] Rule

test1 :: IO ()
test1 = do
  let vars1 = [(Var "x1" Int)]
  let vars2 = [(Var "x2" Int)]
  let vars3 = [(Var "x3" Int)]
  let vars4 = [(Var "x4" Int)]
  let vars4 = [(Var "x5" Int)]
  let n1 = Nonterminal 0 vars1
  let n2 = Nonterminal 1 vars2
  let n3 = Nonterminal 2 vars3
  let n4 = Nonterminal 3 vars4
  let n5 = Nonterminal 4 vars4
  let r1 = Rule n4 (LBool True) [n2]
  let r2 = Rule n4 (LBool True) [n3] 
  let r3 = Rule n2 (LBool True) [n1] 
  let r4 = Rule n3 (LBool True) [n1] 
  let r5 = Rule n5 (LBool True) [n4]
  let g = mkGraph (Grammar 0 [r1,r2,r3,r4,r5])
  let result = toplogicalSort g
  print (shortPrint result)
  let (graph,_) = constructCDD 10 g
  plot "./dotfile1" g
  plot "./dotfile2" graph
  plot2 "./dotfile3" graph
  
test2 :: IO ()
test2 = do
  let vars1 = [(Var "x1" Int)]
  let vars2 = [(Var "x2" Int)]
  let vars3 = [(Var "x3" Int)]
  let vars4 = [(Var "x4" Int)]
  let n1 = Nonterminal 0 vars1
  let n2 = Nonterminal 1 vars2
  let n3 = Nonterminal 2 vars3
  let n4 = Nonterminal 3 vars4
  let r1 = Rule n4 (LBool True) [n2,n3]
  let r2 = Rule n2 (LBool True) [n1] 
  let r3 = Rule n3 (LBool True) [n1] 
  let g = mkGraph (Grammar 0 [r1,r2,r3])
  let result = toplogicalSort g
  print (shortPrint result)
  let (graph,_) = constructCDD 10 g
  plot "./dotfile1" g
  plot "./dotfile2" graph
  plot2 "./dotfile3" graph

test3 :: IO ()
test3 = do
  let vars1 = [(Var "x1" Int)]
  let vars2 = [(Var "x2" Int)]
  let vars3 = [(Var "x3" Int)]
  let vars4 = [(Var "x4" Int)]
  let vars5 = [(Var "x5" Int)]
  let n1 = Nonterminal 1 vars1
  let n2 = Nonterminal 2 vars2
  let n3 = Nonterminal 3 vars3
  let n4 = Nonterminal 4 vars4
  let n5 = Nonterminal 5 vars5
  let r1 = Rule n2 (LBool True) [n1]
  let r2 = Rule n3 (LBool True) [n1] 
  let r3 = Rule n4 (LBool True) [n2]
  let r4 = Rule n4 (LBool True) [n3]
  let r5 = Rule n5 (LBool True) [n4]
  let r6 = Rule n1 (LBool True) [n4]
  let g = mkGraph (Grammar 0 [r1,r2,r3,r4,r5,r6])
  let unwindGraph = mkGraph (Grammar 0 [r1,r2,r3,r4,r5])
  plot "./dotfile1" g
  let newMap1 = foldr (\n m-> M.insert n n m) M.empty [n1,n2,n3,n4,n5]
  let newMap2 = foldr (\n m-> M.insert n [n] m) M.empty [n1,n2,n3,n4,n5]
  unwindResult <- dagUnwind [r6] 10 (CloneInfo newMap1 newMap2) M.empty g unwindGraph
  case unwindResult of
    Just (UnwindResult _ _ nextUnwind) ->do plot "./dotfile2" unwindGraph
                                            plot "./dotfile3" nextUnwind
    Nothing -> error "this is wrong"

test4 :: IO ()
test4 = do
  let vars1 = [(Var "x1" Int)]
  let vars2 = [(Var "x2" Int)]
  let vars3 = [(Var "x3" Int)]
  let vars4 = [(Var "x4" Int)]
  let vars5 = [(Var "x5" Int)]
  let n1 = Nonterminal 1 vars1
  let n2 = Nonterminal 2 vars2
  let n3 = Nonterminal 3 vars3
  let n4 = Nonterminal 4 vars4
  let n5 = Nonterminal 5 vars5
  let r1 = Rule n2 (LBool True) [n1]
  let r2 = Rule n3 (LBool True) [n1] 
  let r3 = Rule n4 (LBool True) [n2]
  let r4 = Rule n4 (LBool True) [n3]
  let r5 = Rule n5 (LBool True) [n4]
  let r6 = Rule n1 (LBool True) [n4]
  let g = mkGraph (Grammar 0 [r1,r2,r3,r4,r5,r6])
  print (backEdges g)
  plot "./dotfile2" g

shortPrint :: [Nonterminal] -> String
shortPrint l = case l of
  [] -> ";"
  x:xs -> (show (_nonterminalSymbol x)) ++ " ," ++ (shortPrint xs)
