{-# LANGUAGE QuasiQuotes #-}

import           Control.Monad.State
import           Data.Map                  (Map)
import qualified Data.Map                  as M
import           Data.Text.Prettyprint.Doc
import           Formula                   hiding (res)
import           Prelude                   hiding (abs, seq)
import           Shara.CDD
import           Shara.Grammar
import           Shara.Interpolate
import qualified Shara.Reg                 as R
import           Shara.Shara
import           System.Environment        (getArgs)

test1 :: SGrammar [Var] Expr
test1 =
  SGrammar
    (STerm [expr|x = 41|] `R.seq` SNonterm ([x], 0))
    (M.fromList
       [ ( 0
         , R.alt
             (STerm [expr|x = 0|])
             (STerm [expr|x = x' + 2|] `R.seq` SNonterm ([x'], 0)))
       ])
  where
    x = Var "x" Int
    x' = Var "x'" Int

test1M :: Map NT [Var]
test1M = M.fromList [(0, [Var "x" Int])]

test2 :: SGrammar [Var] Expr
test2 =
  SGrammar
    (SNonterm ([n, res], m) `R.seq` STerm [expr|res < 0|])
    (M.fromList
       [ ( m
         , mconcat
             [ SNonterm ([n, abs'], l9)
             , SNonterm ([x, d], dbl)
             , STerm [expr|abs' = x && res = d|]
             ])
       , ( l9
         , R.alt
             (SNonterm ([n, abs], l8) `R.seq` STerm [expr|abs' = (0 - n)|])
             (SNonterm ([n, abs], l6) `R.seq` STerm [expr|abs' = n|]))
       , (l8, SNonterm ([n, abs], l4) `R.seq` STerm [expr|n < 0|])
       , (l6, SNonterm ([n, abs], l4) `R.seq` STerm [expr|n >= 0|])
       , (l4, STerm [expr|abs = 0|])
       , (dbl, STerm [expr|d = 2 * x|])
       ])
  where


test2M :: Map NT [Var]
test2M =
  M.fromList
    [ (m, [n, res])
    , (l9, [n, abs'])
    , (l8, [n, abs])
    , (l6, [n, abs])
    , (l4, [n, abs])
    , (dbl, [x, d])
    ]

m = 0

dbl = 1

l9 = 2

l8 = 3

l6 = 4

l4 = 5

n = Var "n" Int

x = Var "x" Int

d = Var "d" Int

abs = Var "abs" Int

abs' = Var "abs'" Int

res = Var "res" Int

main :: IO ()
main = do
  sk <-
    getArgs >>=
    (\as ->
       pure $
       case as of
         [a] ->
           if a == "topo"
             then Topological
             else if a == "par"
                    then LicketySplit ConcurrentInterpolation
                    else LicketySplit SequentialInterpolation
         _ -> LicketySplit SequentialInterpolation)
  print sk
  shara sk test2M test2 >>= \case
    Left m -> print (fmap pretty m)
    Right m -> print (fmap pretty m)
