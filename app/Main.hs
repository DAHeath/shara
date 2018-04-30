{-# LANGUAGE QuasiQuotes #-}

import           Control.Monad.State
import           Data.IntMap                 (IntMap)
import qualified Data.IntMap                 as M
import qualified Data.Language.Reg           as R
import qualified Data.Language.ScopedGrammar as SG
import           Data.Text.Prettyprint.Doc
import           Formula                     hiding (res)
import           Prelude                     hiding (abs)
import           Shara.Interpolate
import           Shara.Shara
import           System.Environment          (getArgs)

test1 :: SG.Grammar [Var] Expr
test1 =
  SG.Grammar
    (SG.Term [expr|x = 41|] `R.seq` SG.Nonterm [x] 0)
    (M.fromList
       [ ( 0
         , R.alt
             (SG.Term [expr|x = 0|])
             (SG.Term [expr|x = x' + 2|] `R.seq` SG.Nonterm [x'] 0))
       ])
  where


test1M :: IntMap [Var]
test1M = M.fromList [(0, [Var "x" Int])]

test2 :: SG.Grammar [Var] Expr
test2 =
  SG.Grammar
    (SG.Nonterm [n, res] m `R.seq` SG.Term [expr|res < 0|])
    (M.fromList
       [ ( m
         , mconcat
             [ SG.Nonterm [n, abs'] l9
             , SG.Nonterm [x, d] dbl
             , SG.Term [expr|abs' = x && res = d|]
             ])
       , ( l9
         , R.alt
             (SG.Nonterm [n, abs] l8 `R.seq` SG.Term [expr|abs' = (0 - n)|])
             (SG.Nonterm [n, abs] l6 `R.seq` SG.Term [expr|abs' = n|]))
       , (l8, SG.Nonterm [n, abs] l4 `R.seq` SG.Term [expr|n < 0|])
       , (l6, SG.Nonterm [n, abs] l4 `R.seq` SG.Term [expr|n >= 0|])
       , (l4, SG.Term [expr|abs = 0|])
       , (dbl, SG.Term [expr|d = 2 * x|])
       ])
  where


test2M :: IntMap [Var]
test2M =
  M.fromList
    [ (m, [n, res])
    , (l9, [n, abs'])
    , (l8, [n, abs])
    , (l6, [n, abs])
    , (l4, [n, abs])
    , (dbl, [x, d])
    ]

m, dbl, l9, l8, l6, l4 :: Int
m = 0

dbl = 1

l9 = 2

l8 = 3

l6 = 4

l4 = 5

n = Var "n" Int

x = Var "x" Int

x' = Var "x'" Int

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
  shara sk test1M test1 >>= \case
    Left m -> print (fmap pretty m)
    Right m -> print (fmap pretty m)
