{-# LANGUAGE TemplateHaskell #-}
module Solver.MinCut where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Monad.Extra (concatMapM)

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

type Symbol = Int

data Graph = Graph
  { _forward   :: Map Symbol (Set Symbol)
  , _backward  :: Map Symbol (Set Symbol)
  , _initials  :: Set Symbol
  , _terminals :: Set Symbol
  } deriving (Show, Read, Eq, Ord)
makeLenses ''Graph

addEdge :: Symbol -> Symbol -> Graph -> Graph
addEdge s t g =
  g & forward  %~ M.insertWith S.union s (S.singleton t)
    & backward %~ M.insertWith S.union t (S.singleton s)

deleteEdge :: Symbol -> Symbol -> Graph -> Graph
deleteEdge s t g =
  g & forward %~ M.adjust (S.delete t) s
    & backward %~ M.adjust (S.delete s) t

addInitial :: Symbol -> Graph -> Graph
addInitial s = initials %~ S.insert s

addTerminal :: Symbol -> Graph -> Graph
addTerminal s = terminals %~ S.insert s

empty :: Graph
empty = Graph M.empty M.empty S.empty S.empty

data CutState = CutState
  { _capacities :: Map (Symbol, Symbol) Rational
  , _weights    :: Map (Symbol, Symbol) Rational
  } deriving (Show, Read, Eq, Ord)
makeLenses ''CutState

type Cut = State CutState

data Direction = Forward | Backward
  deriving (Show, Read, Eq, Ord)

data ExploreCtxt = ExploreCtxt
  { _direction :: Direction
  , _visited :: Set Symbol
  , _cutState :: CutState
  , _theGraph :: Graph
  } deriving (Show, Read, Eq, Ord)
makeLenses ''ExploreCtxt

type Edge = (Symbol, Symbol, Direction)

edges :: Graph -> [(Symbol, Symbol)]
edges g =
  concatMap (\(s, ts) -> [(s, t) | t <- S.toList ts]) (M.toList (view forward g))

symbols :: Graph -> Set Symbol
symbols g = M.keysSet (view forward g `M.union` view backward g)

-- | Given a mapping from edges to capicities and a graph, construct a minimum cut. The
-- minimum cut generates:
--  1) the vertices which are on the cut
--  2) the vertices prior to the cut
--  3) the vertices after the cut
mincut :: Map (Symbol, Symbol) Rational -> Graph -> (Set Symbol, Set Symbol, Set Symbol)
mincut caps g =
  let residual = foldr modGraph g (edges g)
      -- The vertices prior to the cut are those reachable in the residual graph.
      prior = explore residual (view initials g)
      -- The cut is those vertices which are successors of the prior vertices
      -- (and are not prior vertices).
      cut = S.unions (map (\s -> search s (view forward g)) (S.toList prior)) S.\\ prior
      -- The vertices after the cut includes all other vertices.
      after = symbols g S.\\ prior S.\\ cut
  in
  if null cut
  then (prior `S.union` after, S.empty, S.empty)
  else (cut, prior, after)

  where
    -- The eventual state which is calculated via the loop.
    finalState :: CutState
    finalState = execState loop (CutState caps M.empty)

    -- Remove all edges which are completely full and add backward edges for non-empty edges.
    modGraph :: (Symbol, Symbol) -> Graph -> Graph
    modGraph (s, t) gr =
      let w = M.findWithDefault 0 (s, t) (view weights finalState)
          c = M.findWithDefault 0 (s, t) (view capacities finalState)
          gr' = if w < c then gr else deleteEdge s t gr
      in if w > 0 then addEdge t s gr' else gr'


    -- A min cut loop. On each loop, we find an augmenting path, find the
    -- bottleneck along that path, and adjust each weight. We do this until no
    -- additional augmenting paths can be found.
    loop :: Cut ()
    loop = do
      cs <- get
      let paths = dfs cs g
      case paths of
        [] -> pure ()
        (p:_) -> do
          bn <- bottleneck p
          mapM_ (adjust bn) p
          loop

    -- How much weight can we add to each edge along this path?
    bottleneck :: Set Edge -> Cut Rational
    bottleneck = fmap minimum . mapM allowed . S.toList

    -- How much more weight can we add (subtract) from the given edge?
    allowed :: Edge -> Cut Rational
    allowed (s, t, d) = case d of
      Forward -> do
        c <- M.findWithDefault 0 (s, t) <$> use capacities
        w <- M.findWithDefault 0 (s, t) <$> use weights
        pure (c - w)
      Backward ->
        M.findWithDefault 0 (t, s) <$> use weights

    -- Adjust the weights of the edges in the path.
    adjust :: Rational -> Edge -> Cut ()
    adjust w (s, t, d) = case d of
      Forward -> weights %= M.insertWith (+) (s, t) w
      Backward -> weights %= M.insertWith (flip (-)) (t, s) w


explore :: Graph -> Set Symbol -> Set Symbol
explore g starts = evalState (S.unions <$> mapM exploreFrom (S.toList starts)) S.empty
  where
    exploreFrom :: Symbol -> State (Set Symbol) (Set Symbol)
    exploreFrom s = do
      vis <- get
      if s `elem` vis
      then pure S.empty
      else do
        let ss = search s (view forward g)
        modify (S.insert s)
        (S.insert s . S.unions) <$> mapM exploreFrom (S.toList ss)

-- | Perform a DFS which repects the contents of the weights and capacities
-- (that is, you cannot explore forwards through a full edge or backward
-- through an empty edge) and that constructs a complete path from an initial
-- vertex to a terminal vertex.
dfs :: CutState -> Graph -> [Set Edge]
dfs cs g =
  let inits = view initials g
      ec = ExploreCtxt Forward S.empty cs g
  in
  -- Start from each initial vertex and concatenate the result.
  runReader (concatMapM dfsFrom (S.toList inits)) ec

dfsFrom :: Symbol -> Reader ExploreCtxt [Set Edge]
dfsFrom s = do
  terms <- view (theGraph . terminals)
  vis <- view visited
  if
    -- If we've already seen this vertex, it is an illegal dfs
    | s `elem` vis -> pure []
    -- If the veretx is terminal, then we're done!
    | s `elem` terms -> pure [S.empty]
    -- Otherwise, we can try to proceed both forward and backward from all
    -- edges connected to this vertex.
    | otherwise -> do
      g <- view theGraph
      succPaths <- concatMapM for $ S.toList (search s (view forward g))
      predPaths <- concatMapM back $ S.toList (search s (view backward g))
      pure (succPaths ++ predPaths)
  where
    -- We can proceed forward when there is capacity left in the edge.
    for :: Symbol -> Reader ExploreCtxt [Set Edge]
    for t = do
      cap <- M.findWithDefault 0 (s, t) <$> view (cutState . capacities)
      weight <- M.findWithDefault 0 (s, t) <$> view (cutState . weights)
      -- We recurse, making sure to add the current edge to the eventual traversal and
      -- noting that we've already seen the current vertex.
      if weight < cap
      then map (S.insert (s, t, Forward)) <$> local (visited %~ S.insert s) (dfsFrom t)
      else pure []

    -- We can proceed backward when there is weight in the edge.
    back :: Symbol -> Reader ExploreCtxt [Set Edge]
    back t = do
      ws <- view (cutState . weights)
      -- Note that we lookup the weight using the forward direction of the edge.
      let w = M.findWithDefault 0 (t, s) ws
      if w > 0
      then map (S.insert (s, t, Backward)) <$> local (visited %~ S.insert s) (dfsFrom t)
      else pure []

search :: Ord k => k -> Map k (Set a) -> Set a
search = M.findWithDefault S.empty

testG :: Graph
testG =
  empty
  & addEdge 0 1
  & addEdge 0 2
  & addEdge 1 2
  & addEdge 1 3
  & addEdge 1 4
  & addEdge 2 4
  & addEdge 3 5
  & addEdge 4 3
  & addEdge 4 5
  & addInitial 0
  & addTerminal 5

testCap :: Map (Symbol, Symbol) Rational
testCap =
  mempty
  & M.insert (0, 1) 10
  & M.insert (0, 2) 10
  & M.insert (1, 2) 2
  & M.insert (1, 3) 4
  & M.insert (1, 4) 8
  & M.insert (2, 4) 9
  & M.insert (3, 5) 10
  & M.insert (4, 3) 6
  & M.insert (4, 5) 10
