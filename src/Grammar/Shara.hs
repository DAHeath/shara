{-# LANGUAGE QuasiQuotes #-}
module Grammar.Shara where

import           Data.Map (Map)
import qualified Data.Map as M

import           Formula hiding (Rule)

import           Grammar.Grammar
import           Grammar.Graph
import           Grammar.Shara.LicketySplit
import           Grammar.Shara.Disjoin
import           Grammar.Shara.Cut

import Data.Text.Prettyprint.Doc

shara :: Expr -> Grammar -> IO (Either Model (Map Symbol Expr))
shara q g =
  let (g', cs) = mkDisjoint g
  in licketySplit q g' >>= \case
    Left m -> pure (Left m)
    Right m -> pure (Right $ collapseSolution cs m)

testChc :: Grammar
testChc = Grammar
  { _grammarStart = 0
  , _grammarRules =
    [ Rule zero [expr|i > n|] [one]
    , Rule one [expr|i = 0|] []
    , Rule one [expr|i = i'+2 && i' <= n|] [two]
    , Rule two [expr|i' = 0|] []
    , Rule two [expr|i' = i''+2 && i'' <= n|] [three]
    , Rule three [expr|i'' = 0|] []
    , Rule three  [expr|i'' = i'''+2 && i''' <= n|] [four]
    , Rule four [expr|i''' = 0|] []
    ]
  }
  where
    zero  = Nonterminal 0 [Var "i" Int]
    one   = Nonterminal 1 [Var "i" Int]
    two   = Nonterminal 2 [Var "i" Int]
    three = Nonterminal 3 [Var "i" Int]
    four  = Nonterminal 4 [Var "i" Int]

runTest :: IO ()
runTest = do
  sol <- licketySplit [expr|not (i = 3)|] testChc
  case sol of
    Left m -> print (pretty (M.toList m))
    Right m -> print (pretty (M.toList m))
