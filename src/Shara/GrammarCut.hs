module Shara.GrammarCut where

import           Control.Lens          hiding (below)
import           Control.Monad.State
import           Data.IntMap           (IntMap)
import qualified Data.IntMap           as IM
import           Data.IntSet           (IntSet)
import qualified Data.IntSet           as S
import           Data.Language.Grammar hiding (null)
import qualified Data.Language.Reg     as R
import           Data.List             (partition)
import           Data.Map              (Map)
import qualified Data.Map              as M
import           Data.Ratio
import qualified Shara.MinCut          as MC

type Symbol = Int

data HyperGraph = HyperGraph
  { graphForward  :: IntMap [Symbol]
  , graphBackward :: IntMap [[Symbol]]
  } deriving (Show, Read, Eq, Ord)

successors :: Symbol -> HyperGraph -> [Symbol]
successors s = IM.findWithDefault [] s . graphForward

predecessors :: Symbol -> HyperGraph -> [[Symbol]]
predecessors s = IM.findWithDefault [] s . graphBackward

symbols :: HyperGraph -> IntSet
symbols g = IM.keysSet (graphForward g) `S.union` IM.keysSet (graphBackward g)

initials :: HyperGraph -> IntSet
initials g = S.filter (\s -> all null (predecessors s g)) (symbols g)

terminals :: HyperGraph -> IntSet
terminals g = symbols g `S.difference` IM.keysSet (graphForward g)

grammarToGraph :: IntSet -> Grammar a -> HyperGraph
grammarToGraph toKeep (Grammar _ rs) = clear $ HyperGraph forw' back'
  where
    back' = fmap ruleSymbols rs
    forw' = foldr addForw IM.empty (IM.toList back')
    addForw :: (Symbol, [[Symbol]]) -> IntMap [Symbol] -> IntMap [Symbol]
    addForw (snk, srcs) m =
      foldr (\src -> IM.insertWith (++) src [snk]) m (concat srcs)
    ruleSymbols :: Rule a -> [[Symbol]]
    ruleSymbols =
      \case
        R.Null -> []
        R.Eps -> []
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
    clear :: HyperGraph -> HyperGraph
    clear (HyperGraph for back) = HyperGraph for' bac'
      where
        for' =
          IM.filterWithKey (\k v -> k `S.member` toKeep && not (null v)) $
          IM.map (filter (`S.member` toKeep)) for
        bac' =
          IM.filterWithKey (\k _ -> k `S.member` toKeep) $
          IM.map (map (filter (`S.member` toKeep))) back

cut :: IntSet -> HyperGraph -> (IntSet, IntSet, IntSet)
cut uncuttable g =
  let (mcg, caps) = mkCutGraph uncuttable g
  in MC.mincut caps mcg

-- | Construct a simple, non-hyper graph and a map of costs from an input
-- hypergraph.
mkCutGraph :: IntSet -> HyperGraph -> (MC.Graph, Map (Symbol, Symbol) Rational)
mkCutGraph uncuttable g
  -- Find each pairing where each pairing represents a hyperedge. The list of
  -- symbols are the sources of the edge and the distinguished symbol is the
  -- sink.
 =
  let pairs =
        concatMap
          (\s -> do
             ps <- predecessors s g
             pure (s, ps))
          (S.toList $ symbols g) :: [(Symbol, [Symbol])]
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
      let below = (snk, IM.findWithDefault 0 snk down)
          aboves = map (\src -> (src, IM.findWithDefault 0 src up)) srcs
      -- To handle the hyperedge, consider the pairing of each source with the
      -- sink individually.
      in foldr (singlePair below aboves) (mcg, cap) srcs
    singlePair ::
         (Symbol, Integer)
      -> [(Symbol, Integer)]
      -> Symbol
      -> (MC.Graph, Map (Symbol, Symbol) Rational)
      -> (MC.Graph, Map (Symbol, Symbol) Rational)
    singlePair (snk, below) aboves src (mcg, cap) =
      let cost =
            if snk `S.member` uncuttable
              then 10000
              else let ([(_, srcUp)], aboves') =
                         partition ((== src) . fst) aboves
                    -- The vertices above the source are dependent on the vertices below the
                    -- sink as well as all vertices above all other sources.
                       allDown = below + sum (map snd aboves')
                    -- The number of dependencies along this partial edge is the product of
                    -- the dependencies above the edge versus those below.
                       numDeps = allDown * srcUp
                    -- The cost of the edge is the inverse of the number of dependencies (or
                    -- some default value if the number of dependencies is 0).
                   in if numDeps == 0
                        then 10000
                        else 1 % numDeps
      in (MC.addEdge src snk mcg, M.insert (src, snk) cost cap)

-- | Calculate the number of symbols above and below each symbol in the graph.
count :: HyperGraph -> (IntMap Integer, IntMap Integer)
count g =
  ( IM.map (toInteger . S.size) $
    execState (mapM_ up (S.toList $ symbols g)) IM.empty
  , IM.map (toInteger . S.size) $
    execState (mapM_ down (S.toList $ symbols g)) IM.empty)
    -- Find the number of symbols above the current symbol.
  where
    up :: Symbol -> State (IntMap IntSet) IntSet
    up s =
      gets (IM.lookup s) >>= \case
        Nothing -> do
          ps <- mapM up (concat $ predecessors s g)
          let allPs = S.unions (S.singleton s : ps)
          _ <- at s <?= allPs
          pure allPs
        Just c -> pure c
    -- `down` is symmetric to `up` with the notable distinction that
    -- predecessors come in lists (since we are dealing with directed hyperedges)
    -- whereas successors do not.
    down :: Symbol -> State (IntMap IntSet) IntSet
    down s =
      gets (IM.lookup s) >>= \case
        Nothing -> do
          ss <- mapM down (successors s g)
          let allSs = S.unions (S.singleton s : ss)
          _ <- at s <?= allSs
          pure allSs
        Just c -> pure c
