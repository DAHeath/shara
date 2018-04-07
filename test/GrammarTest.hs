import           Control.Monad
import           Control.Applicative
import           Data.Grammar as G

import           Data.Semigroup

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "a grammar rule" $ do
    describe "monoid" $ do
      it "left identity" $ property rMonoidLeftId
      it "right identity" $ property rMonoidRightId
      it "associativity" $ property rMonoidAssoc
    describe "alternative" $ do
      it "left identity" $ property rAltLeftId
      it "right identity" $ property rAltRightId
      it "associativity" $ property rAltAssoc
    describe "monad" $ do
      it "left identity" $ property rMonadLeftId
      it "right identity" $ property rMonadRightId
      it "associativity" $ property rMonadAssoc
  describe "a context free grammar" $ do
    describe "monoid" $ do
      it "left identity" $ property gMonoidLeftId
      it "right identity" $ property gMonoidRightId
      it "associativity" $ property gMonoidAssoc
    describe "alternative" $ do
      it "left identity" $ property gAltLeftId
      it "right identity" $ property gAltRightId
      it "associativity" $ property gAltAssoc
    describe "monad" $ do
      it "left identity" $ property gMonadLeftId
      it "right identity" $ property gMonadRightId
      it "associativity" $ property gMonadAssoc
    describe "partition and connect" $
      it "connect inverts partition" $ property connectPartition

rMonoidLeftId :: Rule Int -> Bool
rMonoidLeftId g = mempty <> g == g

rMonoidRightId :: Rule Int -> Bool
rMonoidRightId g = g <> mempty == g

rMonoidAssoc :: Rule Int -> Rule Int -> Rule Int -> Bool
rMonoidAssoc a b c = a <> (b <> c) == (a <> b) <> c

rAltLeftId :: Rule Int -> Bool
rAltLeftId g = (empty <|> g) == g

rAltRightId :: Rule Int -> Bool
rAltRightId g = (g <|> empty) == g

rAltAssoc :: Rule Int -> Rule Int -> Rule Int -> Bool
rAltAssoc a b c = (a <|> (b <|> c)) == ((a <|> b) <|> c)

rMonadLeftId :: Fun Int (Rule Int) -> Int -> Bool
rMonadLeftId f x =
  let f' = apply f
  in (pure x >>= f') == (f' x :: Rule Int)

rMonadRightId :: Rule Int -> Bool
rMonadRightId g = (g >>= pure) == g

rMonadAssoc :: Rule Int -> Fun Int (Rule Int) -> Fun Int (Rule Int) -> Bool
rMonadAssoc x f g =
  let f' = apply f
      g' = apply g
  in (x >>= f' >>= g') == (x >>= (f' >=> g'))

gMonoidLeftId :: Grammar Int -> Bool
gMonoidLeftId g = mempty <> g == g

gMonoidRightId :: Grammar Int -> Bool
gMonoidRightId g = g <> mempty == g

gMonoidAssoc :: Grammar Int -> Grammar Int -> Grammar Int -> Bool
gMonoidAssoc a b c = a <> (b <> c) == (a <> b) <> c

gAltLeftId :: Grammar Int -> Bool
gAltLeftId g = (empty <|> g) == g

gAltRightId :: Grammar Int -> Bool
gAltRightId g = (g <|> empty) == g

gAltAssoc :: Grammar Int -> Grammar Int -> Grammar Int -> Bool
gAltAssoc a b c = (a <|> (b <|> c)) == ((a <|> b) <|> c)

gMonadLeftId :: Fun Int (Grammar Int) -> Int -> Bool
gMonadLeftId f x =
  let f' = apply f
  in (pure x >>= f') == (f' x :: Grammar Int)

gMonadRightId :: Grammar Int -> Bool
gMonadRightId g = (g >>= pure) == g

gMonadAssoc :: Grammar Int -> Fun Int (Grammar Int) -> Fun Int (Grammar Int) -> Bool
gMonadAssoc x f g =
  let f' = apply f
      g' = apply g
  in (x >>= f' >>= g') == (x >>= (f' >=> g'))

connectPartition :: [NT] -> Grammar Int -> Bool
connectPartition nts g = uncurry (connect nts) (partition nts g) == g
