module Shara.Interpolate where

import           Control.Concurrent.Async (concurrently)
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map                 (Map)
import qualified Data.Map                 as M
import           Data.Set (Set)
import qualified Data.Set                 as S
import           Formula
import qualified Formula.Z3               as Z3
import           Shara.Grammar
import           Shara.GrammarCut
import qualified Shara.Reg                as R

data InterpolationStrategy
  = SequentialInterpolation
  | ConcurrentInterpolation
  deriving (Show, Read, Eq, Ord)

-- | `licketySplit` computes interpolants of a DAG. It attempts to do this
-- maximally in parallel by cutting the DAG consideration at each iteration.
licketySplit ::
     MonadIO m
  => InterpolationStrategy
  -> Grammar Expr
  -> m (Either Model (Map NT Expr))
licketySplit strategy g =
  let ss = nonterminals g in
      liftIO (loop strategy ss g (reverseRules g) M.empty)

-- | The core loop for interpolating a DAG. The loop requires two versions of
-- the DAG, one which is a full representation and another which is a
-- restricted version that only contains a subset of the vertices.
-- On each iteration, the loop cuts the restricted subset using a minimum cut
-- algorithm. Those vertices along the cut are interpolated as a part of the
-- current iteration. The two subgraphs on either side of the cut are the new
-- restrictions which can be interpolated in parallel.
loop ::
     InterpolationStrategy
  -> Set NT
  -> Grammar Expr
  -> Map NT [(Maybe NT, Rule Expr)]
  -> Map NT Expr
  -> IO (Either Model (Map NT Expr))
loop strategy targets g rev m = do
  if null (targets S.\\ M.keysSet m)
    then pure (Right m)
    else do
      let gr = clear (targets S.\\ M.keysSet m) $ grammarToGraph g
      -- let gr = grammarToGraph g
      let (now, half1, half2) = cut gr
      runStateT (runExceptT $ mapM_ (\nt -> interpolateNT' g rev nt) now) m >>=
      -- We only proceed when none of the solved symbols failed.
       \case
        (Left m', _) -> pure (Left m')
        (_, m') -> do
          (m1, m2) <-
            evaluator (loop strategy half1 g rev m') (loop strategy half2 g rev m')
        -- A simple union of the two maps suffices since there should be no
        -- possibility that the two subiterations computed interpolants for the
        -- same vertices.
          pure (M.union <$> m1 <*> m2)
  where
    evaluator =
      case strategy of
        SequentialInterpolation -> sequentially
        ConcurrentInterpolation -> concurrently

-- Replace `concurrently` by this to perform the same action without parallelism.
sequentially :: IO a -> IO b -> IO (a, b)
sequentially a b = do
  a' <- a
  b' <- b
  pure (a', b')

topologicalInterpolation ::
     MonadIO m => Grammar Expr -> m (Either Model (Map NT Expr))
topologicalInterpolation g =
  let rg = reverseRules g
      nts = topologicalOrder g
  in runStateT (runExceptT $ mapM_ (\nt -> interpolateNT' g rg nt) nts) M.empty >>= \case
       (Left m, _) -> pure (Left m)
       (_, m) -> pure (Right m)

interpolateNT' ::
     MonadIO m
  => Grammar Expr
  -> Map NT [(Maybe NT, Rule Expr)]
  -> NT
  -> ExceptT Model (StateT (Map NT Expr) m) ()
interpolateNT' g rg target = do
  solns <- get
  interpolateNT solns g rg target >>= \case
    Left m -> throwError m
    Right phi -> modify (M.insert target phi)

-- | Interpolate the given nonterminal in the context of the directly solvable
-- grammar.
interpolateNT ::
     MonadIO m
  => Map NT Expr
  -> Grammar Expr
  -> Map NT [(Maybe NT, Rule Expr)]
  -> NT
  -> m (Either Model Expr)
interpolateNT solns g rg target =
  let phi1 = mkForm target solns g
      phi2 = mkRevForm target solns g rg
   in Z3.interpolate phi2 phi1

mkForm :: NT -> Map NT Expr -> Grammar Expr -> Expr
mkForm st m g = evalState (ruleExpr m g (ruleFor st g)) S.empty

mark :: NT -> Expr
mark nt = V $ Var ("__b" ++ show nt) Bool

mkRevForm ::
     NT -> Map NT Expr -> Grammar Expr -> Map NT [(Maybe NT, Rule Expr)] -> Expr
mkRevForm st m g rg =
  evalState
    (manyAnd <$> mapM go (M.findWithDefault [] st rg))
    S.empty
  where
    go (Nothing, e) = ruleExpr m g e
    go (Just nt, e) = case M.lookup nt m of
                        Nothing -> do
                          let e' = mkRevForm nt m g rg
                          r' <- ruleExpr m g e
                          pure (manyAnd [ e', mark nt, mkImpl (mark nt) r' ])
                        Just phi -> mkAnd (mkNot phi) <$> (ruleExpr m g e)

ruleExpr :: MonadState (Set NT) m => Map NT Expr -> Grammar Expr -> Rule Expr -> m Expr
ruleExpr m g r = do
  (r', impls) <- go r
  pure $ manyAnd (r' : impls)
  where
    go =
      \case
        R.Seq a b -> do
          (a', aIs) <- go a
          (b', bIs) <- go b
          pure (mkAnd a' b', aIs ++ bIs)
        R.Alt a b -> do
          (a', aIs) <- go a
          (b', bIs) <- go b
          pure (mkOr a' b', aIs ++ bIs)
        R.Eps -> pure (LBool True, [])
        R.Null -> pure (LBool False, [])
        Term t -> pure (t, [])
        Nonterm nt -> handleNT nt
    handleNT nt =
      elem nt <$> get >>= \case
        True -> pure (mark nt, [])
        False -> do
          modify (S.insert nt)
          (phi, is) <-
            case M.lookup nt m of
              Nothing -> go (ruleFor nt g)
              Just phi' -> pure (phi', [])
          pure (mark nt, (mkImpl (mark nt) phi) : is)
