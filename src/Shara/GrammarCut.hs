module Shara.GrammarCut where

import           Control.Lens        hiding (below)
import           Control.Monad.State
import           Data.List           (partition)
import           Data.Map            (Map)
import qualified Data.Map            as M
import           Data.Ratio
import           Data.Set            (Set)
import qualified Data.Set            as S
import           Shara.Grammar       hiding (partition)
import qualified Shara.MinCut        as MC
import qualified Shara.Reg           as R

type Symbol = Int

data HyperGraph = HyperGraph
  { graphForward  :: Map Symbol [Symbol]
  , graphBackward :: Map Symbol [[Symbol]]
  } deriving (Show, Read, Eq, Ord)

successors :: Symbol -> HyperGraph -> [Symbol]
successors s = M.findWithDefault [] s . graphForward

predecessors :: Symbol -> HyperGraph -> [[Symbol]]
predecessors s = M.findWithDefault [] s . graphBackward

symbols :: HyperGraph -> Set Symbol
symbols g = M.keysSet (graphForward g) `S.union` M.keysSet (graphBackward g)

initials :: HyperGraph -> Set Symbol
initials g = S.filter (\s -> all null (predecessors s g)) (symbols g)

terminals :: HyperGraph -> Set Symbol
terminals g = symbols g `S.difference` M.keysSet (graphForward g)

clear :: Set Symbol -> HyperGraph -> HyperGraph
clear toClear (HyperGraph for back) = HyperGraph for' back'
  where
    for' =
      M.filterWithKey (\k _ -> k `notElem` toClear) $
      fmap (filter (`notElem` toClear)) for
    back' =
      M.filterWithKey (\k _ -> k `notElem` toClear) $
      fmap (map (filter (`notElem` toClear))) back

grammarToGraph :: Grammar a -> HyperGraph
grammarToGraph (SGrammar _ rs) = HyperGraph forw back
  where
    back = fmap ruleSymbols rs
    forw = foldr addForw M.empty (M.toList back)
    addForw ::
         (Symbol, [[Symbol]]) -> Map Symbol [Symbol] -> Map Symbol [Symbol]
    addForw (snk, srcs) m =
      foldr (\src -> M.insertWith (++) src [snk]) m (concat srcs)
    ruleSymbols :: Rule a -> [[Symbol]]
    ruleSymbols =
      \case
        R.Null -> []
        R.Eps -> []
        R.Neg a -> ruleSymbols a
        R.Alt a b -> ruleSymbols a ++ ruleSymbols b
        R.Seq a b ->
          let as = ruleSymbols a
              bs = ruleSymbols b
          in if null as
               then bs
               else if null bs
                      then as
                      else [a' ++ b' | a' <- as, b' <- bs]
        Nonterm nt -> [[nt]]
        Term _ -> []

cut :: HyperGraph -> (Set Symbol, Set Symbol, Set Symbol)
cut g =
  let (mcg, caps) = mkCutGraph g
  in MC.mincut caps mcg

-- | Construct a simple, non-hyper graph and a map of costs from an input
-- hypergraph.
mkCutGraph :: HyperGraph -> (MC.Graph, Map (Symbol, Symbol) Rational)
mkCutGraph g
  -- Find each pairing where each pairing represents a hyperedge. The list of
  -- symbols are the sources of the edge and the distinguished symbol is the
  -- sink.
 =
  let pairs =
        concatMap
          (\s -> do
             ps <- predecessors s g
             pure (s, ps))
          (symbols g) :: [(Symbol, [Symbol])]
      -- The basic graph has the same initial and terminal symbols as the hypergraph.
      is = initials g
      ts = terminals g
      mcg = MC.empty & MC.initials .~ is & MC.terminals .~ ts
  -- To build up the graph, look at each hyperedge.
  in foldr handlePair (mcg, M.empty) pairs
    -- Count up the number of vertices above and below each vertex.
  where
    (up, down) = count g
    -- Modify the result due to the effects of a hyperedge.
    handlePair ::
         (Symbol, [Symbol])
      -> (MC.Graph, Map (Symbol, Symbol) Rational)
      -> (MC.Graph, Map (Symbol, Symbol) Rational)
    handlePair (snk, srcs) (mcg, cap) =
      let below = (snk, M.findWithDefault 0 snk down)
          aboves = map (\src -> (src, M.findWithDefault 0 src up)) srcs
      -- To handle the hyperedge, consider the pairing of each source with the
      -- sink individually.
      in foldr (singlePair below aboves) (mcg, cap) srcs
    singlePair ::
         (Symbol, Integer)
      -> [(Symbol, Integer)]
      -> Symbol
      -> (MC.Graph, Map (Symbol, Symbol) Rational)
      -> (MC.Graph, Map (Symbol, Symbol) Rational)
    singlePair (snk, below) aboves src (mcg, cap)
      -- Find the distinguished source's above count and separate it from the others.
     =
      let ([(_, srcUp)], aboves') = partition ((== src) . fst) aboves
          -- The vertices above the source are dependent on the vertices below the
          -- sink as well as all vertices above all other sources.
          allDown = below + sum (map snd aboves')
          -- The number of dependencies along this partial edge is the product of
          -- the dependencies above the edge versus those below.
          numDeps = allDown * srcUp
          -- The cost of the edge is the inverse of the number of dependencies (or
          -- some default value if the number of dependencies is 0).
          cost =
            if numDeps == 0
              then 1
              else 1 % numDeps
      in (MC.addEdge src snk mcg, M.insert (src, snk) cost cap)

-- | Calculate the number of symbols above and below each symbol in the graph.
count :: HyperGraph -> (Map Symbol Integer, Map Symbol Integer)
count g =
  ( execState (mapM_ up (symbols g)) M.empty
  , execState (mapM_ down (symbols g)) M.empty)
    -- Find the number of symbols above the current symbol.
  where
    up :: Symbol -> State (Map Symbol Integer) Integer
    up s =
      M.lookup s <$> get >>= \case
        Nothing
        -- If we haven't found the answer yet, compute across the predecessors,
        -- add 1, and insert it to the map.
         -> do
          ps <- mapM up (concat $ predecessors s g)
          at s <?= (sum ps + toInteger (length ps))
        Just c -> pure c
    -- `down` is symmetric to `up` with the notable distinction that
    -- predecessors come in lists (since we are dealing with directed hyperedges)
    -- whereas successors do not.
    down :: Symbol -> State (Map Symbol Integer) Integer
    down s =
      M.lookup s <$> get >>= \case
        Nothing
        -- If we haven't found the answer yet, compute across the predecessors,
        -- add 1, and insert it to the map.
         -> do
          ss <- mapM down (successors s g)
          at s <?= (sum ss + toInteger (length ss))
        Just c -> pure c
