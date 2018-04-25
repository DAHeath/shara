{-# LANGUAGE QuasiQuotes #-}

import           Control.Monad.State
import           Data.Map                  (Map)
import qualified Data.Map                  as M
import           Data.Text.Prettyprint.Doc
import           Formula
import           Prelude                   hiding (seq)
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
    Left m -> print m
    Right m -> print (fmap pretty m)
  -- evalStateT
  --   (do g <- cdd test1
  --       liftIO $ print (finitePrefix g)
  --       g' <- unrollCDD g
  --       liftIO $ print (finitePrefix g')
  --       liftIO $ print (reverseRules $ finitePrefix g'))
  --   (emptyCDDState test1M)
