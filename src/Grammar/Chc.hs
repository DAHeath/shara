{-# LANGUAGE QuasiQuotes #-}
module Grammar.Chc where

import           Control.Lens
import           Control.Monad.Except

import           Data.Map (Map)
import qualified Data.Map as M

import           Formula hiding (Rule)
import qualified Formula as F
import qualified Formula.Z3 as Z3

import           Grammar.Grammar

import Data.Text.Prettyprint.Doc

runSystem :: [Chc] -> IO (Either Model (Map Symbol Expr))
runSystem clauses = do
  liftIO $ print (pretty clauses)
  runExceptT (interpretModel <$> Z3.solveChc clauses)
  where
    interpretModel m =
      M.mapKeys (read . tail)
      $ M.filterWithKey (\k _ -> head k == 'R')
      $ M.mapKeys _varName m

clause :: Rule -> Chc
clause (Rule lhs f rhs) = F.Rule (map app rhs) f (app lhs)

app :: Nonterminal -> App
app (Nonterminal sym vs) = mkApp ("R" ++ show sym) vs

interpolate :: MonadIO m => Grammar -> m (Either Model (Map Symbol Expr))
interpolate g =
  liftIO (runSystem
    (F.Query [app terminal] (LBool True) [expr|@termQ:Bool|]
    : map clause (g ^. grammarRules)))
  where
    terminal = view ruleLHS (head $ rulesFor (g ^. grammarStart)
                                             (g ^. grammarRules))
    termQ = last (view nonterminalVars terminal)
