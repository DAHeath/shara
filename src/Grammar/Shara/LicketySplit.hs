module Grammar.Shara.LicketySplit (anyOrder, licketySplit, InterpolationStrategy(..)) where

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

data InterpolationStrategy
  = SequentialInterpolation
  | ConcurrentInterpolation
  deriving (Show, Read, Eq, Ord)

-- | `licketySplit` computes interpolants of a DAG. It attempts to do this
-- maximally in parallel by cutting the DAG consideration at each iteration.
licketySplit :: MonadIO m
             => InterpolationStrategy
             -> Expr -> Grammar -> m (Either Model (Map Symbol Expr))
licketySplit strategy q g = do
  let m = M.singleton (g ^. grammarStart) q
  -- Kick off the core loop with a restricted version of the graph that
  -- includes everything except the query.
  liftIO (loop strategy gr initRestricted m)
  where
    gr = mkGraph g
    restriction = S.delete (view grammarStart g) (symbols gr)
    initRestricted = restrict restriction gr

-- | The core loop for interpolating a DAG. The loop requires two versions of
-- the DAG, one which is a full representation and another which is a
-- restricted version that only contains a subset of the vertices.
-- On each iteration, the loop cuts the restricted subset using a minimum cut
-- algorithm. Those vertices along the cut are interpolated as a part of the
-- current iteration. The two subgraphs on either side of the cut are the new
-- restrictions which can be interpolated in parallel.
loop :: InterpolationStrategy
     -> Graph -> Graph -> Map Symbol Expr -> IO (Either Model (Map Symbol Expr))
loop strategy g restricted m =
  if null (symbols restricted S.\\ M.keysSet m)
  then pure (Right m)
  else do
    let (now, rest1, rest2) = cut restricted
    runReaderT (runExceptT (foldrM interp m now)) g >>= \case
      -- We only proceed when none of the solved symbols failed.
      Left m' -> pure (Left m')
      Right m' -> do
        (m1, m2) <- evaluator (loop strategy g (restrict rest1 restricted) m')
                              (loop strategy g (restrict rest2 restricted) m')
        -- A simple union of the two maps suffices since there should be no
        -- possibility that the two subiterations computed interpolants for the 
        -- same vertices.
        pure (M.union <$> m1 <*> m2)
  where
    evaluator = case strategy of
      SequentialInterpolation -> sequentially
      ConcurrentInterpolation -> concurrently

-- Replace `concurrently` by this to perform the same action without parallelism.
sequentially :: IO a -> IO b -> IO (a, b)
sequentially a b = do
  a' <- a
  b' <- b
  pure (a', b')

anyOrder :: MonadIO m => Expr -> Grammar -> m (Either Model (Map Symbol Expr))
anyOrder q g = liftIO $ runReaderT (runExceptT (foldrM interp m now)) gr
  where
    gr = mkGraph g
    m = M.singleton (g ^. grammarStart) q
    now = S.delete (g^. grammarStart) (symbols gr)

-- | Interpolate a particular vertex in the graph.
interp :: Symbol -> Map Symbol Expr -> Solve (Map Symbol Expr)
interp s sols = do
  -- Collect the forward dependencies.
  f <- forward sols s
  -- Collect the backward dependencies.
  b <- backward sols s
  -- Construct an interpolant of these two dependency sets and add it to the map.
  liftIO (interpolate f b) >>= \case
    Left m -> throwError m
    Right e -> pure (M.insert s e sols)

-- | Collect the forward dependencies of a particular vertex. In addition to
-- this set of dependencies containing everything below the current vertex, it
-- also includes all siblings.
forward :: Map Symbol Expr -> Symbol -> Solve Expr
forward sols s =
  case M.lookup s sols of
    Nothing -> do
      rs <- forwardRules s <$> ask
      manyOr <$> mapM (\r -> do
        for <- forward sols (r ^. ruleLHS . nonterminalSymbol)
        -- Collect the siblings by going backwards through the sibling branch.
        back <- mapM (backward sols) $
          filter (/= s) (r ^.. ruleRHS . traverse . nonterminalSymbol)
        pure (manyAnd (for : (r ^. ruleBody) : back))) rs
    Just e -> pure (mkNot e)

-- | Collect the backward dependencies of a particular vertex.
backward :: Map Symbol Expr -> Symbol -> Solve Expr
backward sols s =
  case M.lookup s sols of
    Nothing -> do
      rs <- backwardRules s <$> ask
      manyOr <$> mapM (\r -> do
        rest <- mapM (backward sols) (r ^.. ruleRHS . traverse . nonterminalSymbol)
        pure (manyAnd ((r ^. ruleBody) : rest))) rs
    Just e -> pure e
