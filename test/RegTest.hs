import           Shara.Reg

import           Data.Proxy
import           Data.Semiring
import           Prelude         hiding (seq)
import           Prop
import           Test.Hspec
import           Test.QuickCheck

main :: IO ()
main =
  hspec $
  describe "regular expression" $ do
    let proxy = Proxy :: Proxy Reg
    monoid (Proxy :: Proxy (Reg Int))
    alternative proxy
    monad proxy
    describe "respects semiring" $ do
      it "commutativity" $ property semiringCommute
      it "additive associativity" $ property semiringPlusAssoc
      it "multiplicative associativity" $ property semiringMultAssoc
      it "additive identity" $ property semiringPlusId
      it "left annihilation" $ property semiringLeftAnn
      it "right annihilation" $ property semiringRightAnn
      it "left multiplicative identity" $ property semiringMultLeftId
      it "right multiplicative identity" $ property semiringMultRightId
      it "left distributivity" $ property semiringLeftDistr
      it "right distributivity" $ property semiringRightDistr

newtype BoolSemi =
  BoolSemi Bool
  deriving (Show, Read, Eq, Ord)

instance Arbitrary BoolSemi where
  arbitrary = BoolSemi <$> arbitrary

instance Monoid BoolSemi where
  mappend (BoolSemi x) (BoolSemi y) = BoolSemi (x || y)
  mempty = BoolSemi False

instance Semiring BoolSemi where
  BoolSemi x <.> BoolSemi y = BoolSemi (x && y)
  one = BoolSemi True

summ :: Semiring a => SReg b a -> a
summ = summary (const id)

semiringCommute :: Reg BoolSemi -> Reg BoolSemi -> Bool
semiringCommute a b = summ (a `seq` b) == summ (b `seq` a)

semiringPlusAssoc :: Reg BoolSemi -> Reg BoolSemi -> Reg BoolSemi -> Bool
semiringPlusAssoc a b c =
  summ (a `alt` (b `alt` c)) == summ ((a `alt` b) `alt` c)

semiringMultAssoc :: Reg BoolSemi -> Reg BoolSemi -> Reg BoolSemi -> Bool
semiringMultAssoc a b c =
  summ (a `seq` (b `seq` c)) == summ ((a `seq` b) `seq` c)

semiringPlusId :: Reg BoolSemi -> Bool
semiringPlusId a = summ (a `alt` Null) == summ a

semiringLeftAnn :: Reg BoolSemi -> Bool
semiringLeftAnn a = summ (Null `seq` a) == summ Null

semiringRightAnn :: Reg BoolSemi -> Bool
semiringRightAnn a = summ (a `seq` Null) == summ Null

semiringMultLeftId :: Reg BoolSemi -> Bool
semiringMultLeftId a = summ (Eps `seq` a) == summ a

semiringMultRightId :: Reg BoolSemi -> Bool
semiringMultRightId a = summ (a `seq` Eps) == summ a

semiringLeftDistr :: Reg BoolSemi -> Reg BoolSemi -> Reg BoolSemi -> Bool
semiringLeftDistr a b c =
  summ (a `seq` (b `alt` c)) == summ ((a `seq` b) `alt` (a `seq` c))

semiringRightDistr :: Reg BoolSemi -> Reg BoolSemi -> Reg BoolSemi -> Bool
semiringRightDistr a b c =
  summ ((a `alt` b) `seq` c) == summ ((a `seq` c) `alt` (b `seq` c))
