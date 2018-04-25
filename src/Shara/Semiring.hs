module Shara.Semiring where

class Semiring a where
  (<.>) :: a -> a -> a
  (<+>) :: a -> a -> a
  zero :: a
  one :: a

instance (Semiring a, Semiring b) => Semiring (a, b) where
  (a, b) <.> (a', b') = (a <.> a', b <.> b')
  (a, b) <+> (a', b') = (a <+> a', b <+> b')
  zero = (zero, zero)
  one = (one, one)
