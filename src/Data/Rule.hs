module Data.Rule where

import           Control.Lens hiding (Empty, elements, (:<))
import           Control.Monad.State
import           Control.Applicative

import           Data.Data (Data)
import           Data.Semigroup

import           Test.QuickCheck hiding (NonEmpty)

import           Prelude hiding (seq, sum, product)

-- | A nonterminal exists to identify rules in the context free grammar.
newtype NT = NT { getNT :: Int }
  deriving (Show, Read, Eq, Ord, Data, Real, Bounded, Enum, Integral, Num)

instance Arbitrary NT where
  arbitrary = do
    topNT <- growingElements [0..5]
    NT <$> elements (0:[1..topNT])

-- | The right hand side of a grammar production.
data Rule a
  -- The rule which recognizes nothing.
  = Null
  -- The rule which only recognizes an empty string.
  | Eps
  -- The rule which recognizes based on either subrule.
  | Alt (Rule a) (Rule a)
  -- The rule which recognizes based on the sequence of subrules.
  | Seq (Rule a) (Rule a)
  -- The rule which recognizes based on the right hand side for the given nonterminal.
  | Nonterminal NT
  -- The rule which recognizes the given symbol.
  | Terminal a
  deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

-- | Is the given rule exactly the rule `Null`?
isNull :: Rule a -> Bool
isNull Null = True
isNull _ = False

-- | Is the given rule exactly the rule `Eps`?
isEps :: Rule a -> Bool
isEps Eps = True
isEps _ = False

-- | `seq` is built over the `Seq` constructor. It respects rule sequence
-- associativity and the fact that `Null` is a 0 element and `Eps` is a 1
-- element.
seq :: Rule a -> Rule a -> Rule a
seq Null _      = Null
seq _ Null      = Null
seq Eps x       = x
seq x Eps       = x
seq (Seq x y) z = Seq x (seq y z)
seq x y         = Seq x y

-- | `alt` is built over the `Alt` constructor. It respects rule alternation
-- associativity and the fact that `Null` is a 1 element and that more than one
-- alternation of `Eps` is redundant.
alt :: Rule a -> Rule a -> Rule a
alt Eps Eps     = Eps
alt Eps x       = alt x Eps
alt Null x      = x
alt x Null      = x
alt (Alt x y) z = Alt x (alt y z)
alt x y         = Alt x y

-- | Find the nonterminal symbols in the rule.
ruleNonterminals :: Rule a -> [NT]
ruleNonterminals  = \case
  Null -> []
  Eps -> []
  Seq x y -> ruleNonterminals x ++ ruleNonterminals y
  Alt x y -> ruleNonterminals x ++ ruleNonterminals y
  Terminal _ -> []
  Nonterminal nt -> [nt]

instance Arbitrary a => Arbitrary (Rule a) where
  arbitrary =
    oneof [ pure Null
          , pure Eps
          , alt <$> arbitrary <*> arbitrary
          , seq <$> arbitrary <*> arbitrary
          , Nonterminal <$> arbitrary
          , Terminal <$> arbitrary
          ]

-- | Rules form a natural monoid based on sequencing where `Eps` is the zero
-- element.
instance Monoid (Rule a) where
  mempty = Eps
  mappend = seq
instance Semigroup (Rule a)

-- | Grammar rules form a natural monad. The intuition behind this monad is
-- that if the terminals of the rules are also grammar rules, we can simply
-- inline their definition to form a larger grammar rule.
instance Monad Rule where
  x >>= f = rjoin (fmap f x)
    where
      rjoin :: Rule (Rule a) -> Rule a
      rjoin = \case
        Null -> Null
        Eps -> Eps
        Alt a b -> alt (rjoin a) (rjoin b)
        Seq a b -> seq (rjoin a) (rjoin b)
        Nonterminal nt -> Nonterminal nt
        Terminal t -> t

-- | Because rules have a bind operation, we can trivially implement
-- `Applicative`. The `pure` definition creates a new rule which only
-- recognizes the given element.
instance Applicative Rule where
  pure = Terminal
  f <*> x = f >>= (`fmap` x)

-- | Rules form a natural alternative based on alternation where `Null` is the
-- zero element.
instance Alternative Rule where
  empty = Null
  (<|>) = alt

-- | Draw a representation of the given rule using the show instance to
-- represent terminals.
drawRule :: Show a => Rule a -> String
drawRule = drawRule' show

-- | Draw a representation of the given rule using the given function to
-- represent terminals.
drawRule' :: (a -> String) -> Rule a -> String
drawRule' f = \case
  Null -> "∅"
  Eps -> "ε"
  Seq x y -> drawRule' f x ++ drawRule' f y
  Alt x y -> "[" ++ drawRule' f x ++ "] | [" ++ drawRule' f y ++ "]"
  Terminal t -> "(" ++ f t ++ ")"
  Nonterminal nt -> "{" ++ drawNT nt ++ "}"

-- | Draw a representation of the given nonterminal by showing the
-- representative integer.
drawNT :: NT -> String
drawNT (NT nt) = show nt
