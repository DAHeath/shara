{-# LANGUAGE QuasiQuotes #-}
module Main where

import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Applicative
import           Control.Arrow (second)

import           Data.Grammar (Grammar, NT, Rule)
import qualified Data.Grammar as G
import           Data.InfGrammar (InfGrammar, InfRule)
import qualified Data.InfGrammar as IG
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Formula hiding (Rule, Chc)

import           Solver.Shara
import           Solver.Chc
import           Solver.Types hiding (DirectState(..))
import           Solver.Interpolate
import           Solver.TreeUnwind

import           System.Environment (getArgs)

import           Data.Text.Prettyprint.Doc

main :: IO ()
main = do
  as <- getArgs
  let defStrat = LicketySplit ConcurrentInterpolation
  let cfg = case as of
        [] -> defStrat
        (a:_) -> case a of
          "topo" -> Topological
          "seq" -> LicketySplit SequentialInterpolation
          _ -> defStrat
  print cfg
  solve cfg test >>= \case
    Left e -> print e
    Right m -> print $ map (second pretty) $ M.toList m

test :: Chc
test =
  G.mkGrammar
  (  G.Terminal (Fact [expr|x = 41|])
  <> G.Terminal (Apply x)
  <> G.Nonterminal 0
  ) $
  M.fromList
    [ (0, scope x (G.Terminal (Fact [expr|x = 0|]))
      <|> scope x' (scope x $ G.Terminal (Fact [expr|x' = x+2|])
                               <> G.Terminal (Apply x)
                               <> G.Nonterminal 0))
    ]
  where
    x = Var "x" Int
    x' = Var "x'" Int


experiment :: IO ()
experiment = runReaderT (evalStateT ( do
  g <- treeUnwind test
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g)

  g' <- IG.unroll S.empty g
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g')

  -- itp <- topologicalInterpolation (IG.finite g')
  -- case itp of
  --   Left m -> liftIO $ print $ pretty (M.toList m)
  --   Right m -> liftIO $ print (map (second pretty) (M.toList m))

  g'' <- IG.unroll S.empty g'
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g'')

  g''' <- IG.unroll S.empty g''
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g''')

  g'''' <- IG.unroll S.empty g'''
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw $ (show . pretty) <$> IG.finite g'''')

  p <- getProof
  liftIO $ print $ G.topologicalOrder p
  liftIO $ putStrLn "\n\n"
  liftIO (putStr $ G.draw p)

  itp <- topologicalInterpolation (IG.finite g''')

  case itp of
    Left m -> liftIO $ print $ pretty (M.toList m)
    Right m -> liftIO $ print (map (second pretty) (M.toList m))
  ) emptyState) emptyCtxt
