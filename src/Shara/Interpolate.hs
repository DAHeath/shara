{-# LANGUAGE TemplateHaskell #-}
module Shara.Interpolate where

import           Control.Lens hiding (Context)
import           Control.Concurrent.Async (concurrently)
import           Control.Monad.Except
import           Control.Monad.State
import           Data.IntMap              (IntMap)
import qualified Data.IntMap              as M
import           Data.IntSet              (IntSet)
import qualified Data.IntSet              as S
import           Data.Language.Grammar
import qualified Data.Language.Reg        as R
import           Data.Semigroup
import           Formula
import qualified Formula.Z3               as Z3
import           Shara.GrammarCut

data LicketySplitOptions = LicketySplitOptions
  -- When lickety split divides the problem in two, should it continue on the
  -- two subproblems concurrently?
  { _concurrentInterpolation :: Bool
  -- If lickety split finds that the current subproblem is treelike, should it
  -- invoke the tree interpolator?
  , _useTreeInterpolator :: Bool
  } deriving (Show, Read, Eq, Ord)
makeLenses ''LicketySplitOptions

-- | `licketySplit` computes interpolants of a DAG. It attempts to do this
-- maximally in parallel by cutting the DAG consideration at each iteration.
licketySplit ::
     MonadIO m
  => LicketySplitOptions
  -> Grammar Expr
  -> m (Either Model (IntMap Expr))
licketySplit opts g =
  let ss = nonterminals g
  in liftIO (loop opts ss g (contextualize g) M.empty)

-- | The core loop for interpolating a DAG. The loop requires two versions of
-- the DAG, one which is a full representation and another which is a
-- restricted version that only contains a subset of the vertices.
-- On each iteration, the loop cuts the restricted subset using a minimum cut
-- algorithm. Those vertices along the cut are interpolated as a part of the
-- current iteration. The two subgraphs on either side of the cut are the new
-- restrictions which can be interpolated in parallel.
loop ::
     LicketySplitOptions
  -> IntSet
  -> Grammar Expr
  -> Context Expr
  -> IntMap Expr
  -> IO (Either Model (IntMap Expr))
loop opts targets g rev m = do
  if treelike (targets S.\\ M.keysSet m) rev
  then treeSolve targets g rev m
   else do
  -- if null (targets S.\\ M.keysSet m)
  --   then pure (Right m)
  --   else do
      let gr = grammarToGraph targets g
      let (now', half1', half2') = cut (M.keysSet m) gr
      let (now, half1, half2) =
            if S.null (now' S.\\ M.keysSet m)
              then (targets S.\\ M.keysSet m, S.empty, S.empty)
              else (now', half1', half2')
      runStateT
        (runExceptT $
         mapM_ (interpolateNT' g rev) (S.toList $ now S.\\ M.keysSet m))
        m >>=
      -- We only proceed when none of the solved symbols failed.
       \case
        (Left m', _) -> pure (Left m')
        (_, m') -> do
          (m1, m2) <-
            evaluator
              (loop opts (now <> half1) g rev m')
              (loop opts (now <> half2) g rev m')
        -- A simple union of the two maps suffices since there should be no
        -- possibility that the two subiterations computed interpolants for the
        -- same vertices.
          pure (M.union <$> m1 <*> m2)
  where
    evaluator =
      case view concurrentInterpolation opts of
        False -> sequentially
        True -> concurrently

treelike :: IntSet -> Context Expr -> Bool
treelike remaining rev =
  all (\nt -> length (contextFor nt rev) <= 1) (S.toList remaining)

treeSolve :: IntSet
          -> Grammar Expr
          -> Context Expr
          -> IntMap Expr
          -> IO (Either Model (IntMap Expr))
treeSolve targets g revg m = undefined
  -- TODO invoke the iZ3 tree interpolator over the current grammar.

-- Replace `concurrently` by this to perform the same action without parallelism.
sequentially :: IO a -> IO b -> IO (a, b)
sequentially a b = do
  a' <- a
  b' <- b
  pure (a', b')

topologicalInterpolation ::
     MonadIO m => Grammar Expr -> m (Either Model (IntMap Expr))
topologicalInterpolation g =
  let rg = contextualize g
      nts = topologicalOrder g
  in runStateT (runExceptT $ mapM_ (interpolateNT' g rg) nts) M.empty >>= \case
       (Left m, _) -> pure (Left m)
       (_, m) -> pure (Right m)

interpolateNT' ::
     MonadIO m
  => Grammar Expr
  -> Context Expr
  -> NT
  -> ExceptT Model (StateT (IntMap Expr) m) ()
interpolateNT' g rg target = do
  solns <- get
  interpolateNT solns g rg target >>= \case
    Left m -> throwError m
    Right phi -> modify (M.insert target phi)

-- | Interpolate the given nonterminal in the context of the directly solvable
-- grammar.
interpolateNT ::
     MonadIO m
  => IntMap Expr
  -> Grammar Expr
  -> Context Expr
  -> NT
  -> m (Either Model Expr)
interpolateNT solns g rg target =
  let phi1 = mkForm target solns g
      phi2 = mkRevForm target solns g rg
  in Z3.interpolate phi2 phi1

mkForm :: NT -> IntMap Expr -> Grammar Expr -> Expr
mkForm st m g = evalState (ruleExpr m g (ruleFor st g)) S.empty

mkRevForm :: NT -> IntMap Expr -> Grammar Expr -> Context Expr -> Expr
mkRevForm st m g rg = evalState (manyAnd <$> mapM go (contextFor st rg)) S.empty
  where
    go (Nothing, e1, e2) = ruleExpr m g (e1 `R.seq` e2)
    go (Just nt, e1, e2) =
      let e = e1 `R.seq` e2
      in case M.lookup nt m of
           Nothing -> do
             let e' = mkRevForm nt m g rg
             r' <- ruleExpr m g e
             pure (manyAnd [e', mark nt, mkImpl (mark nt) r'])
           Just phi -> mkAnd (mkNot phi) <$> ruleExpr m g e

ruleExpr ::
     MonadState IntSet m => IntMap Expr -> Grammar Expr -> Rule Expr -> m Expr
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
      gets (S.member nt) >>= \case
        True -> pure (mark nt, [])
        False -> do
          modify (S.insert nt)
          (phi, is) <-
            case M.lookup nt m of
              Nothing -> go (ruleFor nt g)
              Just phi' -> pure (phi', [])
          pure (mark nt, mkImpl (mark nt) phi : is)

mark :: NT -> Expr
mark nt = V $ Var ("__b" ++ show nt) Bool
