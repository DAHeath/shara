module Data.InfGrammar where

import           Control.Lens
import           Control.Monad.State
import           Control.Applicative

import           Data.Semigroup
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)

import           Data.Grammar (Grammar, Rule)
import qualified Data.Grammar as G

type InfGrammar m a = Grammar (Inf m a)
type InfRule m a = Rule (Inf m a)

data Inf m a
  = Finite a
  | Infinite (m (InfGrammar m a))

finite :: InfGrammar m a -> Grammar a
finite (G.Grammar st rs) = G.mkGrammar (finR st) (fmap finR rs)
  where
    finR :: InfRule m a -> Rule a
    finR = \case
      G.Null -> G.Null
      G.Eps -> G.Eps
      G.Alt x y -> finR x <|> finR y
      G.Seq x y -> finR x <> finR y
      G.Nonterminal nt -> G.Nonterminal nt
      G.Terminal (Finite a) -> G.Terminal a
      G.Terminal (Infinite _) -> G.Null

-- TODO ignore nonterminals in the given set.
unroll :: Monad m => Set G.NT -> InfGrammar m a -> m (InfGrammar m a)
unroll noUnroll (G.Grammar st rs) =
  uncurry G.mkGrammar <$> runStateT (M.traverseWithKey lunr rs >> unr st) M.empty
  where
    lunr :: Monad m => G.NT -> InfRule m a -> StateT (Map G.NT (InfRule m a)) m ()
    lunr nt r = do
      r' <- unr r
      modify (M.unionWith (<|>) (M.singleton nt r'))

    unr :: Monad m => InfRule m a -> StateT (Map G.NT (InfRule m a)) m (InfRule m a)
    unr = \case
      G.Null -> pure G.Null
      G.Eps -> pure G.Eps
      G.Seq x y -> (<>) <$> unr x <*> unr y
      G.Alt x y -> (<|>) <$> unr x <*> unr y
      G.Nonterminal nt -> pure (G.Nonterminal nt)
      G.Terminal (Finite t) -> pure (G.Terminal $ Finite t)
      G.Terminal (Infinite ac) -> do
        G.Grammar st' rs' <- lift ac
        modify (M.unionWith (<|>) rs')
        pure st'

fin :: a -> InfRule m a
fin = G.Terminal . Finite

inf :: m (InfGrammar m a) -> InfRule m a
inf = G.Terminal . Infinite

testInf :: InfGrammar IO Int
testInf =
  G.mkGrammar
    (fin 1 <> G.Nonterminal 1)
    (M.fromList
      [(1, inf readRs <|> fin 2) ])
  where
    readRs :: IO (InfGrammar IO Int)
    readRs = do
      n <- read <$> getLine
      pure (pure (Finite n))
