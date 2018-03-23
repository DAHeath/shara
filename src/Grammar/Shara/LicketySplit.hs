module Grammar.Shara.LicketySplit where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.Except

import           Control.Concurrent.Async (concurrently)

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Foldable (foldrM)

import           Formula hiding (Rule)
import           Formula.Z3 (interpolate)

import           Grammar.Grammar
import           Grammar.Graph
import           Grammar.Shara.Cut

type Solve a = ExceptT Model (ReaderT Graph IO) a

licketySplit :: MonadIO m
             => Expr -> Grammar -> m (Either Model (Map Symbol Expr))
licketySplit q g = do
  let m = M.singleton (g ^. grammarStart) q
  liftIO (step 0 (mkGraph g) (mkGraph g) m)

step :: Int -> Graph -> Graph -> Map Symbol Expr -> IO (Either Model (Map Symbol Expr))
step c g restricted m =
  if null (symbols restricted S.\\ M.keysSet m)
  then pure (Right m)
  else do
    let (now, rest1, rest2) = cut restricted
    runReaderT (runExceptT (foldrM interpSym m now)) g >>= \case
      Left m' -> pure (Left m')
      Right m' -> do
      -- We only proceed when none of the solved symbols failed.
        (m1, m2) <- concurrently (step (c+1) g (restrict rest1 restricted) m')
                                 (step (c+1) g (restrict rest2 restricted) m')
        pure (M.union <$> m1 <*> m2)

-- This is for debugging without using parallel.
concurrently' :: IO a -> IO b -> IO (a, b)
concurrently' a b = do
  a' <- a
  b' <- b
  pure (a', b')

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
      rs <- forwardRules s <$> ask
      manyOr <$> mapM (\r -> do
        for <- forward sols (r ^. ruleLHS . nonterminalSymbol)
        back <- mapM (backward sols) $
          filter (/= s) (r ^.. ruleRHS . traverse . nonterminalSymbol)
        pure (manyAnd (for : (r ^. ruleBody) : back))) rs
    Just e -> pure (mkNot e)

backward :: Map Symbol Expr -> Symbol -> Solve Expr
backward sols s =
  case M.lookup s sols of
    Nothing -> do
      rs <- backwardRules s <$> ask
      manyOr <$> mapM (\r -> do
        rest <- mapM (backward sols) (r ^.. ruleRHS . traverse . nonterminalSymbol)
        pure (manyAnd ((r ^. ruleBody) : rest))) rs
    Just e -> pure e
