module Data.Grammar where

import           Control.Lens hiding (Empty, elements, (:<))
import           Control.Monad.State
import           Control.Monad.Writer (Writer, runWriter, tell)
import           Control.Applicative

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Semigroup
import           Data.List (intercalate, nub)

import           Test.QuickCheck hiding (NonEmpty)

import           Prelude hiding (seq, sum, product)

import Debug.Trace

newtype NT = NT { getNT :: Int }
  deriving (Show, Read, Eq, Ord, Data, Real, Bounded, Enum, Integral, Num)

instance Arbitrary NT where
  arbitrary = do
    topNT <- growingElements [0..3]
    NT <$> elements (0:[1..topNT])

data Rule a
  = Null
  | Eps
  | Alt (Rule a) (Rule a)
  | Seq (Rule a) (Rule a)
  | Nonterminal NT
  | Terminal a
  deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

isNull :: Rule a -> Bool
isNull Null = True
isNull _ = False

isEps :: Rule a -> Bool
isEps Eps = True
isEps _ = False

seq :: Rule a -> Rule a -> Rule a
seq Null _      = Null
seq _ Null      = Null
seq Eps x       = x
seq x Eps       = x
seq (Seq x y) z = Seq x (seq y z)
seq x y         = Seq x y

alt :: Rule a -> Rule a -> Rule a
alt Eps Eps     = Eps
alt Eps x       = alt x Eps
alt Null x      = x
alt x Null      = x
alt (Alt x y) z = Alt x (alt y z)
alt x y         = Alt x y

instance Arbitrary a => Arbitrary (Rule a) where
  arbitrary =
    oneof [ pure Null
          , pure Eps
          , alt <$> arbitrary <*> arbitrary
          , seq <$> arbitrary <*> arbitrary
          , Nonterminal <$> arbitrary
          , Terminal <$> arbitrary
          ]

instance Monoid (Rule a) where
  mempty = Eps
  mappend = seq
instance Semigroup (Rule a)

instance Alternative Rule where
  empty = Null
  (<|>) = alt

instance Applicative Rule where
  pure = Terminal
  f <*> x = f >>= (`fmap` x)

rjoin :: Rule (Rule a) -> Rule a
rjoin = \case
  Null -> Null
  Eps -> Eps
  Alt x y -> alt (rjoin x) (rjoin y)
  Seq x y -> seq (rjoin x) (rjoin y)
  Nonterminal nt -> Nonterminal nt
  Terminal t -> t

instance Monad Rule where
  x >>= f = rjoin (fmap f x)

data Grammar a = Grammar
  { start :: Rule a
  , rules :: Map NT (Rule a)
  } deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

mkGrammar :: Rule a -> Map NT (Rule a) -> Grammar a
mkGrammar st rs =
  let g = Grammar st rs
      r = reaching g
      rs' = M.filterWithKey (\k _ -> k `elem` r) rs
      g' = Grammar st rs'
  in clean g'

clean :: Grammar a -> Grammar a
clean (Grammar st rs) =
  let (g', Any change) = runWriter (Grammar <$> go rs st <*> traverse (go rs) rs)
      g'' = case g' of
        Grammar st' rs' ->
          Grammar st' (M.filter (\r -> not (isNull r || isEps r)) rs')
  in if change then clean g'' else g''
  where
    go :: Map NT (Rule a) -> Rule a -> Writer Any (Rule a)
    go m = \case
      Null -> pure Null
      Eps -> pure Eps
      Alt r1 r2 -> alt <$> go m r1 <*> go m r2
      Seq r1 r2 -> seq <$> go m r1 <*> go m r2
      Nonterminal nt -> case M.findWithDefault Null nt m of
        Null -> tell (Any True) >> pure Null
        Eps -> tell (Any True) >> pure Eps
        _ -> pure (Nonterminal nt)
      Terminal t -> pure (Terminal t)

reaching :: Grammar a -> Set NT
reaching (Grammar st rs) = execState (go S.empty) (S.fromList $ ruleNonterminals st)
  where
    go :: Set NT -> State (Set NT) ()
    go v = do
      s <- get
      case S.minView (s S.\\ v) of
        Nothing -> pure ()
        Just (nt, _) -> do
          let r = M.findWithDefault Null nt rs
          modify (S.union (S.fromList $ ruleNonterminals r))
          go (S.insert nt v)

ruleFor :: NT -> Grammar a -> Rule a
ruleFor nt (Grammar _ rs) = M.findWithDefault Null nt rs

gjoin :: Grammar (Grammar a) -> Grammar a
gjoin (Grammar st rs) =
  uncurry mkGrammar $ runState (M.traverseWithKey joinLRule rs >> joinRule st) M.empty
  where
    joinLRule nt r = do
      r' <- joinRule r
      modify (M.unionWith alt (M.singleton nt r'))

    joinRule Null = pure Null
    joinRule Eps = pure Eps
    joinRule (Seq x y) = do
      y' <- joinRule y
      x' <- joinRule x
      pure (seq x' y')
    joinRule (Alt x y) = do
      y' <- joinRule y
      x' <- joinRule x
      pure (alt x' y')
    joinRule (Nonterminal nt) = pure $ Nonterminal nt
    joinRule (Terminal (Grammar st' rs')) = do
      modify (M.unionWith alt rs')
      pure st'

singleton :: a -> Grammar a
singleton x = Grammar (Terminal x) M.empty

nullGrammar :: Grammar a
nullGrammar = Grammar Null M.empty

instance Applicative Grammar where
  pure = singleton
  f <*> x = f >>= (`fmap` x)

instance Monad Grammar where
  x >>= f = gjoin $ fmap f x

product :: Grammar a -> Grammar a -> Grammar a
product (Grammar st rs) (Grammar st' rs') =
  Grammar (seq st st') (M.unionWith alt rs rs')

sum :: Grammar a -> Grammar a -> Grammar a
sum (Grammar st rs) (Grammar st' rs') =
  Grammar (alt st st') (M.unionWith alt rs rs')

instance Semigroup (Grammar a)

instance Monoid (Grammar a) where
  mempty = Grammar Eps M.empty
  mappend = product

instance Alternative Grammar where
  empty = Grammar Null M.empty
  (<|>) = sum

addRule :: NT -> Rule a -> Grammar a -> Grammar a
addRule nt r (Grammar st rs) = mkGrammar st (M.insertWith alt nt r rs)

addStart :: Rule a -> Grammar a -> Grammar a
addStart s (Grammar st rs) = mkGrammar (alt s st) rs

instance Arbitrary a => Arbitrary (Grammar a) where
  arbitrary = do
    nRules <- growingElements [0..4]
    nStarts <- growingElements [0..3]
    sts <- replicateM nStarts arbitrary
    let nts = nub $ concatMap ruleNonterminals sts
    rs <- if null nts
          then pure []
          else evalStateT (replicateM nRules arbRule) nts
    pure $ foldr addStart (foldr (uncurry addRule) empty rs) sts
    where
      arbRule :: Arbitrary a => StateT [NT] Gen (NT, Rule a)
      arbRule = do
        choices <- get
        lhs <- lift (elements choices)
        rhs <- lift arbitrary
        modify (nub . (ruleNonterminals rhs ++))
        pure (lhs, rhs)

ruleNonterminals :: Rule a -> [NT]
ruleNonterminals  = \case
  Null -> []
  Eps -> []
  Seq x y -> ruleNonterminals x ++ ruleNonterminals y
  Alt x y -> ruleNonterminals x ++ ruleNonterminals y
  Terminal _ -> []
  Nonterminal nt -> [nt]

nonterminals :: Grammar a -> Set NT
nonterminals = undefined -- TODO

abstract :: NT -> Grammar a -> Grammar a
abstract nt (Grammar st rs) =
  Grammar (Nonterminal nt) (M.insert nt st rs)

drawRule :: Show a => Rule a -> String
drawRule = \case
  Null -> "∅"
  Eps -> "ε"
  Seq x y -> drawRule x ++ drawRule y
  Alt x y -> "[" ++ drawRule x ++ "] | [" ++ drawRule y ++ "]"
  Terminal t -> "(" ++ show t ++ ")"
  Nonterminal nt -> "{" ++ drawNT nt ++ "}"

draw :: Show a => Grammar a -> String
draw (Grammar st rs) =
  drawRule st ++ "\n" ++ unlines (map drawRule' (M.toList rs))
  where
    drawRule' (nt, r) = drawNT nt ++ ": " ++ drawRule r

drawNT :: NT -> String
drawNT (NT nt) = show nt

test :: Grammar Int
test =
  mkGrammar
    (Terminal 1 `seq` Nonterminal 1)
    (M.fromList
      [(1, Terminal 3 `alt` Terminal 2) ])
