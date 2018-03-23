module Grammar.Shara.Cut where

import           Control.Lens hiding (below)
import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List (partition)
import           Data.Ratio

import           Grammar.Grammar hiding (predecessors, successors)
import           Grammar.Graph
import qualified Grammar.Shara.MinCut as MC

cut :: Graph -> (Set Symbol, Set Symbol, Set Symbol)
cut g =
  case length (symbols g) of
    0 -> (S.empty, S.empty, S.empty)
    1 -> (symbols g, S.empty, S.empty)
    _ ->
      let (mcg, caps) = mkCutGraph g
      in MC.mincut caps mcg

-- | Construct a simple, non-hyper graph and a map of costs from an input
-- hypergraph.
mkCutGraph :: Graph -> (MC.Graph, Map (Symbol, Symbol) (Maybe Rational))
mkCutGraph g =
  -- Find each pairing where each pairing represents a hyperedge. The list of
  -- symbols are the sources of the edge and the distinguished symbol is the
  -- sink.
  let pairs = concatMap (\s -> do
        ps <- predecessors s g
        pure (s, ps)) (symbols g) :: [(Symbol, [Symbol])]
      -- The basic graph has the same initial and terminal symbols as the hypergraph.
      is = initials g
      ts = terminals g
      mcg = MC.empty & MC.initials .~ is
                     & MC.terminals .~ ts
  in
  -- To build up the graph, look at each hyperedge.
  foldr handlePair (mcg, M.empty) pairs

  where
    -- Count up the number of vertices above and below each vertex.
    (up, down) = count g

    -- Modify the result due to the effects of a hyperedge.
    handlePair :: (Symbol, [Symbol]) -> (MC.Graph, Map (Symbol, Symbol) (Maybe Rational))
                                     -> (MC.Graph, Map (Symbol, Symbol) (Maybe Rational))
    handlePair (snk, srcs) (mcg, cap) =
      let below = (snk, M.findWithDefault 0 snk down)
          aboves = map (\src -> (src, M.findWithDefault 0 src up)) srcs
      in
      -- To handle the hyperedge, consider the pairing of each source with the
      -- sink individually.
      foldr (singlePair below aboves) (mcg, cap) srcs

    singlePair :: (Symbol, Integer)
               -> [(Symbol, Integer)]
               -> Symbol
               -> (MC.Graph, Map (Symbol, Symbol) (Maybe Rational))
               -> (MC.Graph, Map (Symbol, Symbol) (Maybe Rational))
    singlePair (snk, below) aboves src (mcg, cap) =
      -- Find the distinguished source's above count and separate it from the others.
      let ([(_, srcUp)], aboves') = partition ((== src) . fst) aboves
          -- The vertices above the source are dependent on the vertices below the
          -- sink as well as all vertices above all other sources.
          allDown = below + sum (map snd aboves')
          -- The number of dependencies along this partial edge is the product of
          -- the dependencies above the edge versus those below.
          numDeps = allDown * srcUp
          -- The cost of the edge is the inverse of the number of dependencies (or
          -- some default value if the number of dependencies is 0).
          cost = if numDeps == 0 then Just 1 else Just (1 % numDeps)
      in (MC.addEdge src snk mcg, M.insert (src, snk) cost cap)

-- | Calculate the number of symbols above and below each symbol in the graph.
count :: Graph -> (Map Symbol Integer, Map Symbol Integer)
count g =
  ( execState (mapM_ up (symbols g)) M.empty
  , execState (mapM_ down (symbols g)) M.empty
  )
  where
    -- Find the number of symbols above the current symbol.
    up :: Symbol -> State (Map Symbol Integer) Integer
    up s = M.lookup s <$> get >>= \case
      Nothing -> do
        -- If we haven't found the answer yet, compute across the predecessors,
        -- add 1, and insert it to the map.
        ps <- mapM up (concat $ predecessors s g)
        at s <?= (sum ps + toInteger (length ps))
      Just c -> pure c

    -- `down` is symmetric to `up` with the notable distinction that
    -- predecessors come in lists (since we are dealing with directed hyperedges)
    -- whereas successors do not.
    down :: Symbol -> State (Map Symbol Integer) Integer
    down s = M.lookup s <$> get >>= \case
      Nothing -> do
        -- If we haven't found the answer yet, compute across the predecessors,
        -- add 1, and insert it to the map.
        ss <- mapM down (successors s g)
        at s <?= (sum ss + toInteger (length ss))
      Just c -> pure c
