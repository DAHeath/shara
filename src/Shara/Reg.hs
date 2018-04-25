module Shara.Reg where

import           Control.Applicative
import           Data.Data           (Data)
import           Data.Semigroup
import           Prelude             hiding (seq)
import           Shara.Inf
import           Shara.Semiring
import           Test.QuickCheck

-- | A finite (no Kleene star) regular expression that supports scoping.
-- Scoping supports operations such as a change of vocabulary in the expression
-- terms.
data Reg a
  = Seq (Reg a)
        (Reg a) -- Sequence two expressions one after the other.
  | Alt (Reg a)
        (Reg a) -- Alternation: Choose one or the other.
  | Neg (Reg a)
  | Eps -- The expression that matches the empty string.
  | Null -- The expression that matches nothing.
  | Symbol a -- The expression that matches exactly the given symbol.
  deriving (Show, Read, Eq, Ord, Data, Foldable, Traversable)

type IReg m a = Infinite m Reg a

-- | Associative sequencing where Null is the a 0 and Eps is a unit.
seq :: Reg a -> Reg a -> Reg a
seq Null _ = Null
seq _ Null = Null
seq Eps x = x
seq x Eps = x
seq (Seq x y) z = Seq x (seq y z)
seq x y = Seq x y

-- | Associative alternation where Null is a unit and Eps is not duplicated.
alt :: Reg a -> Reg a -> Reg a
alt Eps Eps = Eps
alt Eps x = alt x Eps
alt Null x = x
alt x Null = x
alt (Alt x y) z = Alt x (alt y z)
alt x y = Alt x y

instance Functor Reg where
  fmap f =
    \case
      Seq a b -> seq (fmap f a) (fmap f b)
      Alt a b -> alt (fmap f a) (fmap f b)
      Neg a -> Neg (fmap f a)
      Null -> Null
      Eps -> Eps
      Symbol a -> Symbol (f a)

-- | Finite regular expressions form a monad where each expression is inlined.
instance Monad Reg where
  x >>= f = join' (fmap f x)
    where
      join' =
        \case
          Seq a b -> seq (join' a) (join' b)
          Alt a b -> alt (join' a) (join' b)
          Neg a -> Neg (join' a)
          Eps -> Eps
          Null -> Null
          Symbol a -> a

-- | Since they form a Monad, regular expressions form an applicative in a
-- straightforward manner.
instance Applicative Reg where
  f <*> x = f >>= (\f' -> x >>= (pure . f'))
  pure = Symbol

instance Semigroup (Reg a)

instance Monoid (Reg a) where
  mempty = Eps
  mappend = seq

instance Alternative (Reg) where
  (<|>) = alt
  empty = Null

instance Arbitrary a => Arbitrary (Reg a) where
  arbitrary =
    oneof
      [ seq <$> arbitrary <*> arbitrary
      , alt <$> arbitrary <*> arbitrary
      , Neg <$> arbitrary
      , pure Eps
      , pure Null
      , Symbol <$> arbitrary
      ]
