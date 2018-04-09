module Data.Grammar
  ( module Data.Grammar
  , module Data.Rule
  ) where

import           Control.Lens hiding (Empty, elements, (:<))
import           Control.Monad.State
import           Control.Applicative

import           Data.Foldable (asum)
import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Semigroup
import           Data.List (nub)

import           Data.Rule

import           Test.QuickCheck

import           Prelude hiding (seq, sum, product)

-- | A Context Free Grammar is a collection of grammar rule productions. The
-- productions are indexed by the Nonterminal Symbols which correspond to the
-- rules. In addition, there is an explicit `start` grammar rule which
-- indicates the entry point to the grammar.
data Grammar a = Grammar
  { start :: Rule a
  , rules :: Map NT (Rule a)
  } deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

-- | Construct a grammar from the given start rule and productions, but do so
-- while respecting a grammar normal form. Specifically, there are no
-- productions which are unreachable from the start rule and `Null` productions
-- are left implicit.
mkGrammar :: Rule a -> Map NT (Rule a) -> Grammar a
mkGrammar st rs =
  let g = Grammar st rs
      r = reaching g
      rs' = M.filter (not . isNull) $ M.filterWithKey (\k _ -> k `elem` r) rs
  in Grammar st rs'

-- | Which nonterminal symbols can be reached from the start production?
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

-- | Lookup the production for the given nonterminal. If the nonterminal has no
-- explicit production, the grammar will indicate this is the case by giving
-- the `Null` rule.
ruleFor :: NT -> Grammar a -> Rule a
ruleFor nt (Grammar _ rs) = M.findWithDefault Null nt rs

-- | Construct a grammar which recognizes a single, given element only.
singleton :: a -> Grammar a
singleton x = Grammar (Terminal x) M.empty

-- | The grammar which recognizes no strings.
nullGrammar :: Grammar a
nullGrammar = Grammar Null M.empty

-- | The grammar which only recognizes the empty string.
epsGrammar :: Grammar a
epsGrammar = Grammar Eps M.empty

-- | Take the product of two grammars: That is, sequence the two start symbols
-- and join their production rules.
product :: Grammar a -> Grammar a -> Grammar a
product (Grammar st rs) (Grammar st' rs') =
  mkGrammar (seq st st') (M.unionWith alt rs rs')

-- | Take the sum of two grammars: That is, alternate the two start symbols
-- and join their production rules.
sum :: Grammar a -> Grammar a -> Grammar a
sum (Grammar st rs) (Grammar st' rs') =
  mkGrammar (alt st st') (M.unionWith alt rs rs')

-- | Grammars form a natural monoid under the product where the epsilon grammar
-- is the unit.
instance Monoid (Grammar a) where
  mempty = Grammar Eps M.empty
  mappend = product
instance Semigroup (Grammar a)

-- | Grammars naturally a monad. The intuition behind this monad instance is
-- that if a terminal in the grammar is itself a grammar, then we can inline
-- the start rule at this location and merge the productions.
instance Monad Grammar where
  x >>= f = gjoin $ fmap f x
    where
      gjoin :: Grammar (Grammar a) -> Grammar a
      gjoin (Grammar st rs) =
        -- Run the inlining procedure over the start and all productions.
        uncurry mkGrammar $ runState (M.traverseWithKey joinLRule rs >> joinRule st) M.empty
        where
          -- Run the inlining procedure over the rule before adding it to the productions.
          joinLRule nt r = joinRule r >>= modify . M.unionWith alt . M.singleton nt

          -- Run the inlining procedure over the rule, amending the productions
            -- whenever there is a terminal symbol.
          joinRule Null = pure Null
          joinRule Eps = pure Eps
          joinRule (Seq a b) = seq <$> joinRule a <*> joinRule b
          joinRule (Alt a b) = alt <$> joinRule a <*> joinRule b
          joinRule (Nonterminal nt) = pure $ Nonterminal nt
          joinRule (Terminal (Grammar st' rs')) = modify (M.unionWith alt rs') >> pure st'

-- | Since we have an implementation for bind, grammars are trivially an
-- Applicative where the unit is the singleton procedure.
instance Applicative Grammar where
  pure = singleton
  f <*> x = f >>= (`fmap` x)

-- | The natural choice for an alternative instance is sum where the null
-- grammar is a unit.
instance Alternative Grammar where
  empty = nullGrammar
  (<|>) = sum

instance Arbitrary a => Arbitrary (Grammar a) where
  arbitrary = do
    nRules <- growingElements [0..6]
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

      addRule :: NT -> Rule a -> Grammar a -> Grammar a
      addRule nt r (Grammar st rs) = mkGrammar st (M.insertWith alt nt r rs)

      addStart :: Rule a -> Grammar a -> Grammar a
      addStart s (Grammar st rs) = mkGrammar (alt s st) rs

-- | Find the set of all nonterminals named in the grammar.
nonterminals :: Grammar a -> Set NT
nonterminals (Grammar st rs) =
  S.fromList $
    ruleNonterminals st ++
    concatMap ruleNonterminals (M.elems rs) ++
    M.keys rs

-- | Abstract performs two important operations on a grammar simultaneously:
-- It moves the start rule into productions for the given nonterminal.
-- It adds a singleton start rule which produces the given nonterminal.
-- The combined effect is that the grammar is now hidden behind the given
-- nonterminal.
abstract :: NT -> Grammar a -> Grammar a
abstract nt (Grammar st rs) =
  mkGrammar (Nonterminal nt) (M.insert nt st rs)

-- | Topologically order the nonterminal symbols in the grammar.
-- Note that this can be done regardless of recursion in the grammar because we
-- know the correct starting location.
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

-- | Partition a grammar into two halves: Those which reach the given list of
-- nonterminals and those that are strictly reached by the list.
partition :: [NT] -> Grammar a -> (Grammar a, Grammar a)
partition nts g = (before, after)
  where
    before = evalState (go (start g)) (S.fromList nts)
    after =
      evalState (asum <$> mapM (\nt -> fmap (abstract nt) $ go $ ruleFor nt g) nts)
        (nonterminals before)
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
connect nts before (Grammar st rs) = before <|> after'
  where
    after' = case reduce nts st of
      Grammar st' rs' -> mkGrammar st' (M.unionWith alt rs rs')
    reduce nts' r =
      case nts' of
        [] -> mkGrammar r M.empty
        [nt] -> mkGrammar Null (M.singleton nt r)
        (nt:nts'') -> case r of
          Alt x y -> mkGrammar Null (M.singleton nt x) <|> reduce nts'' y
          x -> mkGrammar Null (M.singleton nt x)

-- | Draw a representation of the grammar using the show instance for terminals.
draw :: Show a => Grammar a -> String
draw = draw' show

-- | Draw a representation of the grammar using the given function for terminals.
draw' :: (a -> String) -> Grammar a -> String
draw' f (Grammar st rs) = unlines (("S: " ++ drawRule' f st) : map drawLRule (M.toList rs))
  where
    drawLRule (nt, r) = drawNT nt ++ ": " ++ drawRule' f r

test :: Grammar Int
test =
  mkGrammar
    (Terminal 1 `seq` Nonterminal 1)
    (M.fromList
      [(1, Terminal 3 `alt` Terminal 2) ])
