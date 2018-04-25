{-# LANGUAGE PatternSynonyms #-}

module Shara.Inf where

import           Control.Monad
import Shara.Semiring

newtype Infinite m f a = Infinite
  { getInfinite :: f (Either a (m (Infinite m f a)))
  }

pattern Fin :: a -> Either a b
pattern Fin a = Left a

pattern Inf :: b -> Either a b
pattern Inf a = Right a

-- | Collect the current finite prefix of the structure by replacing infinite
-- elements by the default structure.
finite :: Monad f => f a -> Infinite m f a -> f a
finite def =
  join .
  fmap
    (\case
       Fin x -> pure x
       Inf _ -> def) .
  getInfinite

unroll ::
     (Applicative m, Monad f, Traversable f)
  => Infinite m f a
  -> m (Infinite m f a)
unroll =
  fmap (Infinite . join) .
  traverse
    (\case
       Fin x -> pure (pure (Fin x))
       Inf ac -> getInfinite <$> ac) .
  getInfinite

type IList m a = Infinite m [] a

singleton :: (Functor m, Applicative f) => m a -> m (Infinite m f a)
singleton x = Infinite . pure . Fin <$> x
