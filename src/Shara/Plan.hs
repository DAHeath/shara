module Shara.Plan where

import           Control.Lens hiding (Context)
import           Control.Monad.Except
import           Control.Monad.State
import           Data.IntMap               (IntMap)
import qualified Data.IntMap               as M
import           Data.IntSet               (IntSet)
import qualified Data.IntSet               as S
import           Data.Language.Grammar
import qualified Data.Language.Reg         as R
import           Data.List.Split
import           Data.Tree                 as Tree
import           Formula
import qualified Formula.Z3                as Z3
import           Shara.Interpolate

data Task
  = Join NT
  | TreeLike (Tree NT)
  deriving (Show, Read, Eq)

interp :: Grammar Expr -> IO (Either Model (IntMap Expr))
interp g = do
  (a, s) <- runStateT (runExceptT (execute g (contextualize g) (plan g))) M.empty
  case a of
    Left m -> pure (Left m)
    Right _ -> pure (Right s)

plan :: Grammar a -> [Task]
plan g = tree (start g) (-1)
  where
    js = joinPoints g
    tree r nt =
      let (t, ijs) = runState (go r nt) S.empty
          rest = concatMap (\n -> tree (ruleFor n g) n) (S.toList ijs)
      in map Join (S.toList ijs) ++ [TreeLike t] ++ rest
    go r nt = do
      let (localJoins, others) =
            S.partition (`S.member` js) (ruleNonterminals r)
      modify (S.union localJoins)
      Tree.Node nt <$> mapM (\n -> go (ruleFor n g) n) (S.toList others)

execute ::
     Grammar Expr
  -> Context Expr
  -> [Task]
  -> ExceptT Model (StateT (IntMap Expr) IO) ()
execute g rev = \case
  [] -> pure ()
  (Join nt:rest) -> interpolateNT' g rev nt >> execute g rev rest
  (TreeLike t:rest) -> interpolateTree g rev t >> execute g rev rest

interpolateTree ::
     Grammar Expr
  -> Context Expr
  -> Tree NT
  -> ExceptT Model (StateT (IntMap Expr) IO) ()
interpolateTree g rev ntTree = do
  let root = Tree.rootLabel ntTree
  m <- get
  let context = case root of
                  (-1) -> localize m (start g)
                  _ -> localRule g m root `mkAnd`
                    mkNot (M.findWithDefault (LBool False) root m)
  let eTree' = case mkETree g m ntTree of
        Tree.Node _ rest -> Tree.Node context rest
  t <- liftIO (Z3.treeInterpolate eTree')
  case t of
    Left m -> throwError m
    Right t' -> modify (M.union (execState (bindTreeResults ntTree t') m))
  where
    bindTreeResults (Tree.Node nt nts) (Tree.Node e es) = do
      when (nt /= Tree.rootLabel ntTree)
        (modify (M.insert nt e))
      mapM_ (uncurry bindTreeResults) (zip nts es)

mkETree :: Grammar Expr -> IntMap Expr -> Tree NT -> Tree Expr
mkETree g m (Tree.Node nt rest) =
  Tree.Node (localRule g m nt) (map (mkETree g m) rest)
  & vars . varName %~ rename
  where
    js = joinPoints g
    rename n =
      if read (last $ splitOn "#" n) `S.member` js
         then n ++ "#" ++ show nt
         else n

localRule :: Grammar Expr -> IntMap Expr -> NT -> Expr
localRule g m nt = localize m (ruleFor nt g)

localize :: IntMap Expr -> Rule Expr -> Expr
localize m = \case
  Nonterm nt -> M.findWithDefault (LBool True) nt m
  R.Seq a b -> localize m a `mkAnd` localize m b
  R.Alt a b -> localize m a `mkOr` localize m b
  R.Eps -> LBool True
  R.Null -> LBool False
  Term t -> t

joinPoints :: Grammar a -> IntSet
joinPoints g = snd $ execState (go $ start g) (S.empty, S.empty)
  where
    go =
      \case
        Nonterm nt -> do
          (vis, js) <- get
          if nt `S.member` vis
            then put (vis, S.insert nt js)
            else do
              put (S.insert nt vis, js)
              go (ruleFor nt g)
        R.Seq a b -> go a >> go b
        R.Alt a b -> go a >> go b
        _ -> pure ()
