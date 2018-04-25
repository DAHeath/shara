{-# LANGUAGE PatternSynonyms #-}

module Shara.Grammar where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Data            (Data)
import           Data.Foldable        (asum)
import           Data.Map             (Map)
import qualified Data.Map             as M
import           Data.Semigroup
import           Data.Set             (Set)
import qualified Data.Set             as S
import           Prelude              hiding (seq)
import           Shara.Inf            (Infinite)
import           Shara.Reg            (Reg)
import qualified Shara.Reg            as R

type NT = Int

type SRule s a = Reg (Either (s, NT) a)

type Rule a = Reg (Either ((), NT) a)

pattern SNonterm :: a -> Reg (Either a b)
pattern SNonterm x = R.Symbol (Left x)
pattern STerm :: b -> Reg (Either a b)
pattern STerm x = R.Symbol (Right x)
pattern Nonterm :: a -> Reg (Either ((), a) b)
pattern Nonterm x = R.Symbol (Left ((), x))
pattern Term :: b -> Reg (Either ((), a) b)
pattern Term x = R.Symbol (Right x)

data SGrammar s a = SGrammar
  { start :: SRule s a
  , rules :: Map NT (SRule s a)
  } deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

type Grammar a = SGrammar () a

type ISGrammar m s a = Infinite m (SGrammar s) a

type IGrammar m a = Infinite m (SGrammar ()) a

seq :: SGrammar s a -> SGrammar s a -> SGrammar s a
seq (SGrammar s rs) (SGrammar s' rs') =
  SGrammar (s `R.seq` s') (M.unionWith R.alt rs rs')

alt :: SGrammar s a -> SGrammar s a -> SGrammar s a
alt (SGrammar s rs) (SGrammar s' rs') =
  SGrammar (s `R.alt` s') (M.unionWith R.alt rs rs')

neg :: SGrammar s a -> SGrammar s a
neg (SGrammar s rs) = SGrammar (R.Neg s) rs

abstract :: s -> NT -> SGrammar s a -> SGrammar s a
abstract sc nt (SGrammar s rs) =
  SGrammar (SNonterm (sc, nt)) (M.insertWith R.alt nt s rs)

singleton :: a -> SGrammar s a
singleton a = SGrammar (STerm a) M.empty

flat :: SRule s a -> SGrammar s a
flat r = SGrammar r M.empty

ruleFor :: NT -> SGrammar s a -> SRule s a
ruleFor nt = M.findWithDefault R.Null nt . rules

after :: NT -> SGrammar s a -> SGrammar s a
after nt g =
  let s = ruleFor nt g
  in SGrammar s (fst $ execState (go s) (M.empty, S.empty))
  where
    go =
      \case
        SNonterm (_, nt') ->
          elem nt' <$> use _2 >>= \case
            True -> pure ()
            False ->
              let r = ruleFor nt' g
              in do _1 %= M.insert nt' r
                    _2 %= S.insert nt'
                    go r
        R.Alt x y -> go x >> go y
        R.Seq x y -> go x >> go y
        _ -> pure ()

-- | This only works for commutative semirings.
reverseRules :: Grammar a -> Map NT (Rule a)
reverseRules g = runReader (go $ start g) R.Eps
  where
    go =
      \case
        R.Seq a b -> do
          M.union <$> local (R.seq b) (go a) <*> local (R.seq a) (go b)
        R.Alt a b -> M.union <$> go a <*> go b
        Nonterm nt -> do
          r <- ask
          M.union <$> local (const (Nonterm nt)) (go (ruleFor nt g)) <*>
            pure (M.singleton nt (R.Neg r))
        _ -> pure mempty

grammarFromMap :: NT -> Map NT (SRule s a) -> SGrammar s a
grammarFromMap st m =
  SGrammar (M.findWithDefault R.Null st m) (M.delete st m)

before :: NT -> SGrammar s a -> SGrammar s a
before nt g =
  let (s, (rs, _)) = runState (go (start g)) (M.empty, S.empty)
  in SGrammar s rs
  where
    go =
      \case
        SNonterm (vs, nt') -> do
          when (nt /= nt') $
            elem nt <$> use _2 >>= \case
              True -> pure ()
              False -> do
                r' <- go (ruleFor nt' g)
                _1 %= M.insert nt' r'
                _2 %= S.insert nt'
          pure (SNonterm (vs, nt'))
        R.Alt x y -> R.alt <$> go x <*> go y
        R.Seq x y -> R.seq <$> go x <*> go y
        x -> pure x

partition :: [NT] -> Grammar a -> (Grammar a, Grammar a)
partition nts g = (bef, aft)
  where
    bef = evalState (go (start g)) (S.fromList nts)
    aft =
      evalState
        (asum <$> mapM (\nt -> fmap (abstract () nt) $ go $ ruleFor nt g) nts)
        (nonterminals bef)
    go =
      \case
        R.Null -> pure empty
        R.Eps -> pure mempty
        R.Seq x y -> (<>) <$> go x <*> go y
        R.Alt x y ->
          (\(SGrammar st rs) (SGrammar st' rs') ->
             SGrammar (R.alt st st') (M.unionWith R.alt rs rs')) <$>
          go x <*>
          go y
        R.Neg x -> go x >>= \case
                     SGrammar st rs -> pure $ SGrammar (R.Neg st) rs
        Term t -> pure $ singleton t
        Nonterm nt -> do
          vis <- get
          r <-
            if nt `elem` vis
              then pure empty
              else go (ruleFor nt g)
          modify (S.insert nt)
          pure (abstract () nt r)

nonterminals :: SGrammar s a -> Set NT
nonterminals (SGrammar st rs) =
  S.unions
    ( ruleNonterminals st
    : M.keysSet rs
    : map ruleNonterminals (M.elems rs)
    )

ruleNonterminals :: SRule s a -> Set NT
ruleNonterminals  = \case
  R.Seq x y -> ruleNonterminals x `S.union` ruleNonterminals y
  R.Alt x y -> ruleNonterminals x `S.union` ruleNonterminals y
  SNonterm (_, nt) -> S.singleton nt
  _ -> S.empty

topologicalOrder :: SGrammar s a -> [NT]
topologicalOrder g = evalState (topo (start g))  S.empty
  where
    topo :: SRule s a -> State (Set NT) [NT]
    topo = \case
      R.Null -> pure []
      R.Eps -> pure []
      R.Seq x y -> (++) <$> topo x <*> topo y
      R.Alt x y -> (++) <$> topo x <*> topo y
      R.Neg x -> topo x
      STerm _ -> pure []
      SNonterm (_, nt) -> (nt `elem`) <$> get >>= \case
        False -> do
          modify (S.insert nt)
          (nt:) <$> topo (ruleFor nt g)
        True -> pure []

instance Monoid (SGrammar s a) where
  mempty = SGrammar R.Eps M.empty
  mappend = seq

instance Semigroup (SGrammar s a)

instance Monad (SGrammar s) where
  x >>= f = gjoin $ fmap f x
    where
      gjoin (SGrammar st rs) =
        uncurry SGrammar $
        runState (M.traverseWithKey joinLRule rs >> joinRule st) M.empty
        where
          joinLRule nt r =
            modify . M.unionWith R.alt . M.singleton nt =<< joinRule r
          joinRule = \case
            R.Null -> pure R.Null
            R.Eps -> pure R.Eps
            R.Seq a b -> R.seq <$> joinRule a <*> joinRule b
            R.Alt a b -> R.alt <$> joinRule a <*> joinRule b
            R.Neg a -> R.Neg <$> joinRule a
            SNonterm nt -> pure $ SNonterm nt
            STerm (SGrammar st' rs') ->
              modify (M.unionWith R.alt rs') >> pure st'

instance Applicative (SGrammar s) where
  pure = singleton
  f <*> x = f >>= (`fmap` x)

-- | The natural choice for an alternative instance is sum where the null
-- grammar is a unit.
instance Alternative (SGrammar s) where
  empty = SGrammar R.Null M.empty
  (<|>) = alt
