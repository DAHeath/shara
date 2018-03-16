module Grammar.Shara.LicketySplit where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.Except

import           Control.Concurrent.Async (concurrently)

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import           Data.Foldable (foldrM)

import           Formula hiding (Rule)
import           Formula.Z3 (interpolate)

import           Grammar.Grammar
import           Grammar.Shara.Cut

type Solve a = ExceptT Model (ReaderT Grammar IO) a

licketySplit :: MonadIO m
             => Expr -> Grammar -> m (Either Model (Map Symbol Expr))
licketySplit q g = do
  let m = M.singleton (g ^. grammarStart) q
  liftIO (step g (allSymbols g) m)

step :: Grammar -> Set Symbol -> Map Symbol Expr
     -> IO (Either Model (Map Symbol Expr))
step g here m =
  if null here
  then pure (Right m)
  else do
    let (now, rest1, rest2) = cut g here
    runReaderT (runExceptT (foldrM interpSym m now)) g >>= \case
      Left m' -> pure (Left m')
      Right m' -> do
      -- We only proceed when none of the solved symbols failed.
        (m1, m2) <- concurrently (step g rest1 m') (step g rest2 m')
        pure (M.union <$> m1 <*> m2)

interpSym :: Symbol -> Map Symbol Expr -> Solve (Map Symbol Expr)
interpSym s sols = do
  f <- forward sols s
  b <- backward sols s
  liftIO (interpolate f b) >>= \case
    Left m -> throwError m
    Right e -> pure (M.insert s e sols)

forward :: Map Symbol Expr -> Symbol -> Solve Expr
forward sols s =
  case M.lookup s sols of
    Nothing -> do
      rs <- rulesWith s . view grammarRules <$> ask
      manyOr <$> mapM (\r -> do
        rest <- forward sols (r ^. ruleLHS . nonterminalSymbol)
        pure (rest `mkAnd` (r ^. ruleBody))) rs
    Just e -> pure (mkNot e)

backward :: Map Symbol Expr -> Symbol -> Solve Expr
backward sols s =
  case M.lookup s sols of
    Nothing -> do
      rs <- rulesFor s . view grammarRules <$> ask
      manyOr <$> mapM (\r -> do
        rest <- mapM (backward sols) (r ^.. ruleRHS . traverse . nonterminalSymbol)
        pure (manyAnd ((r ^. ruleBody) : rest))) rs
    Just e -> pure e
