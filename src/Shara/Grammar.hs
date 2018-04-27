{-# LANGUAGE PatternSynonyms #-}

module Shara.Grammar where

import           Control.Arrow
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

abstract :: s -> NT -> SGrammar s a -> SGrammar s a
abstract sc nt (SGrammar s rs) =
  SGrammar (SNonterm (sc, nt)) (M.insertWith R.alt nt s rs)

singleton :: a -> SGrammar s a
singleton a = SGrammar (STerm a) M.empty

flat :: SRule s a -> SGrammar s a
flat r = SGrammar r M.empty

ruleFor :: NT -> SGrammar s a -> SRule s a
ruleFor nt = M.findWithDefault R.Null nt . rules

reverseRules :: Grammar a -> Map NT [(Maybe NT, Rule a)]
reverseRules g = runReader (go $ start g) (Nothing, R.Eps)
  where
    go =
      \case
        R.Seq a b -> do
          M.unionWith (++) <$> local (second (R.seq b)) (go a) <*> local (second (R.seq a)) (go b)
        R.Alt a b -> M.union <$> go a <*> go b
        Nonterm nt -> do
          ctx <- ask
          M.unionWith (++) <$> local (const (Just nt, R.Eps)) (go (ruleFor nt g)) <*>
            pure (M.singleton nt [ctx])
        _ -> pure mempty

grammarFromMap :: NT -> Map NT (SRule s a) -> SGrammar s a
grammarFromMap st m =
  SGrammar (M.findWithDefault R.Null st m) (M.delete st m)

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
