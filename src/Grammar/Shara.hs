{-# LANGUAGE QuasiQuotes #-}
module Grammar.Shara where

-- import           Control.Monad.IO.Class

-- import           Data.Map (Map)
-- import qualified Data.Map as M
-- import           Data.Set (Set)

-- import           Formula hiding (Rule)

-- import           Grammar.Grammar
-- import           Grammar.Shara.LicketySplit
-- import           Grammar.Shara.TreeUnwind

-- import Data.Text.Prettyprint.Doc

-- data SharaCfg = SharaCfg
--   { interpolator :: Interpolator
--   , unwindStrategy :: UnwindStrategy
--   } deriving (Show, Read, Eq, Ord)

-- data Interpolator
--   = LicketySplit InterpolationStrategy
--   | AnyOrder
--   deriving (Show, Read, Eq, Ord)

-- data UnwindStrategy
--   = TreeUnwind
--   | DisjointDependencyUnwind
--   deriving (Show, Read, Eq, Ord)

-- shara :: Expr -> Grammar -> IO (Either Model (Map Symbol Expr))
-- shara = shara' defaultCfg
--   where
--     defaultCfg =
--       SharaCfg
--       { interpolator = LicketySplit ConcurrentInterpolation
--       , unwindStrategy = TreeUnwind
--       -- TODO swap this
--       }

-- shara' :: SharaCfg -> Expr -> Grammar -> IO (Either Model (Map Symbol Expr))
-- shara' cfg q g = do
--   let (q', g', cs) = unwindGrammar (unwindStrategy cfg) q g
--   solveGrammar (interpolator cfg) q' g' >>= \case
--     Left m -> pure (Left m)
--     Right m -> pure (Right m)
--     -- TODO collapse solution

-- unwindGrammar :: UnwindStrategy -> Expr -> Grammar -> (Expr, Grammar, Map Symbol (Set Symbol))
-- unwindGrammar DisjointDependencyUnwind = undefined
-- unwindGrammar TreeUnwind = treeUnwind

-- solveGrammar :: MonadIO m => Interpolator -> Expr -> Grammar -> m (Either Model (Map Symbol Expr))
-- solveGrammar (LicketySplit strategy) = licketySplit strategy
-- solveGrammar AnyOrder = anyOrder

-- testChc :: Grammar
-- testChc = Grammar
--   { _grammarStart = 0
--   , _grammarRules =
--     [ Rule zero [expr|i > n|] [one]
--     , Rule one [expr|i = 0|] []
--     , Rule one [expr|i = i'+2 && i' <= n|] [Nonterminal 2 [Var "i'" Int]]
--     , Rule two [expr|i = 0|] []
--     , Rule two [expr|i = i'+2 && i' <= n|] [Nonterminal 3 [Var "i'" Int]]
--     , Rule three [expr|i = 0|] []
--     , Rule three  [expr|i = i'+2 && i' <= n|] [Nonterminal 4 [Var "i'" Int]]
--     , Rule four [expr|i = 0|] []
--     ]
--   }
--   where
--     zero  = Nonterminal 0 [Var "i" Int]
--     one   = Nonterminal 1 [Var "i" Int]
--     two   = Nonterminal 2 [Var "i" Int]
--     three = Nonterminal 3 [Var "i" Int]
--     four  = Nonterminal 4 [Var "i" Int]

-- runTest :: IO ()
-- runTest = do
--   sol <- shara [expr|not (i = 3)|] testChc
--   case sol of
--     Left m -> print (pretty (M.toList m))
--     Right m -> print (pretty (M.toList m))
