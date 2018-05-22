{-# LANGUAGE TemplateHaskell #-}
module Shara.Interpolate where

import           Control.Lens hiding (Context)
import           Control.Concurrent.Async (concurrently)
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Reader
import           Data.IntMap              (IntMap)
import qualified Data.IntMap              as M
import           Data.IntSet              (IntSet)
import qualified Data.IntSet              as S
import           Data.Language.Grammar
import qualified Data.Language.Reg        as R
import           Data.Semigroup
import           Data.Tree as Tree
import           Data.List.Split (splitOn)
import           Formula
import qualified Formula.Z3               as Z3

type Interpolate a =
  ReaderT (Grammar Expr, Context Expr) (ExceptT Model (StateT (IntMap Expr) IO)) a

interpolate :: Grammar Expr -> IO (Either Model (IntMap Expr))
interpolate g = do
  (a, s) <-
    runStateT (
      runExceptT (
        runReaderT execute (g, contextualize g)
   )) M.empty
  case a of
    Left m -> pure (Left m)
    Right _ -> pure (Right s)

execute :: Interpolate ()
execute = do
  g <- asks fst
  tree (start g) (-1)
  where
    tree r nt = do
      g <- asks fst
      jps <- joinPoints
      let (t, js) = runState (go jps g r nt) S.empty
      mapM_ interpolateNT (S.toList js)
      interpolateTree t
      mapM_ (\n -> tree (ruleFor n g) n) (S.toList js)
    go jps g r nt = do
      let (localJoins, others) =
            S.partition (`S.member` jps) (ruleNonterminals r)
      modify (S.union localJoins)
      Tree.Node nt <$> mapM (\n -> go jps g (ruleFor n g) n) (S.toList others)

interpolateTree :: Tree NT -> Interpolate ()
interpolateTree ntTree = do
  let root = Tree.rootLabel ntTree
  context <- case root of
               (-1) -> localize =<< asks (start . fst)
               _ -> do
                 loc <- localRule root
                 ctxt <- gets (M.findWithDefault (LBool False) root)
                 pure (loc `mkAnd` mkNot ctxt)
  eTree <- mkETree ntTree >>= \case
        Tree.Node _ rest -> pure $ Tree.Node context rest
  liftIO (Z3.treeInterpolate eTree) >>= \case
    Left m -> throwError m
    Right t -> bindTreeResults ntTree t
  where
    bindTreeResults (Tree.Node nt nts) (Tree.Node e es) = do
      when (nt /= Tree.rootLabel ntTree)
        (modify (M.insert nt e))
      mapM_ (uncurry bindTreeResults) (zip nts es)

mkETree :: Tree NT -> Interpolate (Tree Expr)
mkETree (Tree.Node nt rest) = do
  rest' <- mapM mkETree rest
  r <- localRule nt
  Tree.Node r rest' & vars . varName %%~ rename
  where
    rename n = do
      jps <- joinPoints
      pure $ if read (last $ splitOn "#" n) `S.member` jps
         then n ++ "#" ++ show nt
         else n

localRule :: NT -> Interpolate Expr
localRule nt = asks (ruleFor nt . fst) >>= localize

localize :: Rule Expr -> Interpolate Expr
localize = \case
  Nonterm nt -> gets (M.findWithDefault (LBool True) nt)
  R.Seq a b -> mkAnd <$> localize a <*> localize b
  R.Alt a b -> mkOr <$> localize a <*> localize b
  R.Eps -> pure $ LBool True
  R.Null -> pure $ LBool False
  Term t -> pure t

joinPoints :: Interpolate IntSet
joinPoints = do
  g <- asks fst
  pure $ snd $ execState (go g $ start g) (S.empty, S.empty)
  where
    go g =
      \case
        Nonterm nt -> do
          (vis, js) <- get
          if nt `S.member` vis
            then put (vis, S.insert nt js)
            else do
              put (S.insert nt vis, js)
              go g (ruleFor nt g)
        R.Seq a b -> go g a >> go g b
        R.Alt a b -> go g a >> go g b
        _ -> pure ()

interpolateNT :: NT -> Interpolate ()
interpolateNT target = do
  phi1 <- mkForm target
  phi2 <- mkRevForm target <$> get <*> asks fst <*> asks snd
  Z3.interpolate phi2 phi1 >>= \case
    Left m -> throwError m
    Right phi -> modify (M.insert target phi)

mkForm :: NT -> Interpolate Expr
mkForm st = do
  g <- asks fst
  m <- get
  pure $ evalState (ruleExpr m g (ruleFor st g)) S.empty

mkRevForm :: NT -> IntMap Expr -> Grammar Expr -> Context Expr -> Expr
mkRevForm st m g rg =
  evalState (manyAnd <$> mapM go (contextFor st rg)) S.empty
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
