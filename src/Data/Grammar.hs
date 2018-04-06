module Data.Grammar where

import           Control.Lens hiding (Empty, elements, (:<))
import           Control.Monad.State
import           Control.Monad.Writer (Writer, runWriter, tell)
import           Control.Applicative

import           Data.Foldable (asum)
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
      rs' = M.filter (not . isNull) $ M.filterWithKey (\k _ -> k `elem` r) rs
  in Grammar st rs'

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
  mkGrammar (seq st st') (M.unionWith alt rs rs')

sum :: Grammar a -> Grammar a -> Grammar a
sum (Grammar st rs) (Grammar st' rs') =
  mkGrammar (alt st st') (M.unionWith alt rs rs')

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
nonterminals (Grammar st rs) =
  S.fromList $
    ruleNonterminals st ++
    concatMap ruleNonterminals (M.elems rs) ++
    M.keys rs

abstract :: NT -> Grammar a -> Grammar a
abstract nt (Grammar st rs) =
  mkGrammar (Nonterminal nt) (M.insert nt st rs)

topologicalOrder :: Grammar a -> [NT]
topologicalOrder g = evalState (topo (start g))  S.empty
  where
    topo :: Rule a -> State (Set NT) [NT]
    topo = \case
      Null -> pure []
      Eps -> pure []
      Seq x y -> (++) <$> topo x <*> topo y
      Alt x y -> (++) <$> topo x <*> topo y
      Terminal _ -> pure []
      Nonterminal nt -> (nt `elem`) <$> get >>= \case
        False -> do
          modify (S.insert nt)
          (nt:) <$> topo (ruleFor nt g)
        True -> pure []

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

-- forall g nts, uncurry (connect nts) (partition nts g) = g

-- | Partition a grammar into two halves: Those which reach the given list of
-- nonterminals and those that are strictly reached by the list.
partition :: [NT] -> Grammar a -> (Grammar a, Grammar a)
partition nts g = (reaching, reached)
  where
    reaching = evalState (go (start g)) (S.fromList nts)
    reached =
      evalState (asum <$> mapM (go . (`ruleFor` g)) nts)
        (nonterminals reaching S.\\ S.fromList nts)
    go = \case
      Null -> pure empty
      Eps -> pure mempty
      Seq x y -> (<>) <$> go x <*> go y
      Alt x y ->
        (\(Grammar st rs) (Grammar st' rs') ->
          mkGrammar (Alt st st') (M.unionWith Alt rs rs')) <$> go x <*> go y
      Terminal t -> pure $ singleton t
      Nonterminal nt -> do
        vis <- get
        r <- if nt `elem` vis
             then pure empty
             else go (ruleFor nt g)
        modify (S.insert nt)
        pure (abstract nt r)

-- | Connect two graphs by mapping each start alternative to a different
-- nonterminal and adding this mapping to the first graph.
connect :: [NT] -> Grammar a -> Grammar a -> Grammar a
connect nts reaching (Grammar st rs) = reaching <|> reached'
  where
    reduce nts r =
      case nts of
        [] -> mkGrammar r M.empty
        [nt] -> mkGrammar Null (M.singleton nt r)
        (nt:nts') -> case r of
          Alt x y -> mkGrammar Null (M.singleton nt x) <|> reduce nts' y
          x -> mkGrammar Null (M.singleton nt x)
    reached' = case reduce nts st of
      Grammar st' rs' -> mkGrammar st' (M.unionWith alt rs rs')

test :: Grammar Int
test =
  mkGrammar
    (Terminal 1 `seq` Nonterminal 1)
    (M.fromList
      [(1, Terminal 3 `alt` Terminal 2) ])
