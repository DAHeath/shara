{-# LANGUAGE TemplateHaskell #-}

module Shara.MinCut where

import           Control.Lens
import           Control.Monad.Extra  (concatMapM)
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.IntMap          (IntMap)
import qualified Data.IntMap          as IM
import           Data.IntSet          (IntSet)
import qualified Data.IntSet          as IS
import           Data.Map             (Map)
import qualified Data.Map             as M
import           Data.Set             (Set)
import qualified Data.Set             as S

type Symbol = Int

data Graph = Graph
  { _forward   :: IntMap IntSet
  , _backward  :: IntMap IntSet
  , _initials  :: IntSet
  , _terminals :: IntSet
  } deriving (Show, Read, Eq, Ord)

makeLenses ''Graph

addEdge :: Symbol -> Symbol -> Graph -> Graph
addEdge s t g =
  g & forward %~ IM.insertWith IS.union s (IS.singleton t) & backward %~
  IM.insertWith IS.union t (IS.singleton s)

deleteEdge :: Symbol -> Symbol -> Graph -> Graph
deleteEdge s t g =
  g & forward %~ IM.adjust (IS.delete t) s & backward %~
  IM.adjust (IS.delete s) t

addInitial :: Symbol -> Graph -> Graph
addInitial s = initials %~ IS.insert s

addTerminal :: Symbol -> Graph -> Graph
addTerminal s = terminals %~ IS.insert s

empty :: Graph
empty = Graph IM.empty IM.empty IS.empty IS.empty

data CutState = CutState
  { _capacities :: Map (Symbol, Symbol) Rational
  , _weights    :: Map (Symbol, Symbol) Rational
  } deriving (Show, Read, Eq, Ord)

makeLenses ''CutState

type Cut = State CutState

data Direction
  = Forward
  | Backward
  deriving (Show, Read, Eq, Ord)

data ExploreCtxt = ExploreCtxt
  { _direction :: Direction
  , _visited   :: IntSet
  , _cutState  :: CutState
  , _theGraph  :: Graph
  } deriving (Show, Read, Eq, Ord)

makeLenses ''ExploreCtxt

type Edge = (Symbol, Symbol, Direction)

edges :: Graph -> [(Symbol, Symbol)]
edges g =
  concatMap
    (\(s, ts) -> [(s, t) | t <- IS.toList ts])
    (IM.toList (view forward g))

symbols :: Graph -> IntSet
symbols g = IM.keysSet (view forward g `IM.union` view backward g)

-- | Given a mapping from edges to capicities and a graph, construct a minimum cut. The
-- minimum cut generates:
--  1) the vertices which are on the cut
--  2) the vertices prior to the cut
--  3) the vertices after the cut
mincut :: Map (Symbol, Symbol) Rational -> Graph -> (IntSet, IntSet, IntSet)
mincut caps g =
  let residual = foldr modGraph g (edges g)
      -- The vertices prior to the cut are those reachable in the residual graph.
      prior = explore residual (view initials g)
      -- The cut is those vertices which are successors of the prior vertices
      -- (and are not prior vertices).
      cut =
        IS.unions (map (\s -> search s (view forward g)) (IS.toList prior)) IS.\\
        prior
      -- The vertices after the cut includes all other vertices.
      after = symbols g IS.\\ prior IS.\\ cut
  in if IS.null cut
       then (prior `IS.union` after, IS.empty, IS.empty)
       else (cut, prior, after)
    -- The eventual state which is calculated via the loop.
  where
    finalState :: CutState
    finalState = execState loop (CutState caps M.empty)
    -- Remove all edges which are completely full and add backward edges for non-empty edges.
    modGraph :: (Symbol, Symbol) -> Graph -> Graph
    modGraph (s, t) gr =
      let w = M.findWithDefault 0 (s, t) (view weights finalState)
          c = M.findWithDefault 0 (s, t) (view capacities finalState)
          gr' =
            if w < c
              then gr
              else deleteEdge s t gr
      in if w > 0
           then addEdge t s gr'
           else gr'
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
    allowed (s, t, d) =
      case d of
        Forward -> do
          c <- M.findWithDefault 0 (s, t) <$> use capacities
          w <- M.findWithDefault 0 (s, t) <$> use weights
          pure (c - w)
        Backward -> M.findWithDefault 0 (t, s) <$> use weights
    -- Adjust the weights of the edges in the path.
    adjust :: Rational -> Edge -> Cut ()
    adjust w (s, t, d) =
      case d of
        Forward -> weights %= M.insertWith (+) (s, t) w
        Backward -> weights %= M.insertWith (flip (-)) (t, s) w

explore :: Graph -> IntSet -> IntSet
explore g starts =
  evalState (IS.unions <$> mapM exploreFrom (IS.toList starts)) IS.empty
  where
    exploreFrom :: Symbol -> State IntSet IntSet
    exploreFrom s = do
      vis <- get
      if s `IS.member` vis
        then pure IS.empty
        else do
          let ss = search s (view forward g)
          modify (IS.insert s)
          IS.insert s . IS.unions <$> mapM exploreFrom (IS.toList ss)

-- | Perform a DFS which repects the contents of the weights and capacities
-- (that is, you cannot explore forwards through a full edge or backward
-- through an empty edge) and that constructs a complete path from an initial
-- vertex to a terminal vertex.
dfs :: CutState -> Graph -> [Set Edge]
dfs cs g =
  let inits = view initials g
      ec = ExploreCtxt Forward IS.empty cs g
  -- Start from each initial vertex and concatenate the result.
  in runReader (concatMapM dfsFrom (IS.toList inits)) ec

dfsFrom :: Symbol -> Reader ExploreCtxt [Set Edge]
dfsFrom s = do
  terms <- view (theGraph . terminals)
  vis <- view visited
    -- If we've already seen this vertex, it is an illegal dfs
  if | s `IS.member` vis -> pure []
     | s `IS.member` terms -> pure [S.empty]
     | otherwise ->
       local (visited %~ IS.insert s) $ do
         g <- view theGraph
         succPaths <- concatMapM for $ IS.toList (search s (view forward g))
         predPaths <- concatMapM back $ IS.toList (search s (view backward g))
         pure (succPaths ++ predPaths)
    -- We can proceed forward when there is capacity left in the edge.
  where
    for :: Symbol -> Reader ExploreCtxt [Set Edge]
    for t = do
      cap <- M.findWithDefault 0 (s, t) <$> view (cutState . capacities)
      weight <- M.findWithDefault 0 (s, t) <$> view (cutState . weights)
      -- We recurse, making sure to add the current edge to the eventual
      -- traversal and noting that we've already seen the current vertex.
      if weight < cap
        then map (S.insert (s, t, Forward)) <$> dfsFrom t
        else pure []
    -- We can proceed backward when there is weight in the edge.
    back :: Symbol -> Reader ExploreCtxt [Set Edge]
    back t = do
      ws <- view (cutState . weights)
      -- Note that we lookup the weight using the forward direction of the edge.
      let w = M.findWithDefault 0 (t, s) ws
      if w > 0
        then map (S.insert (s, t, Backward)) <$> dfsFrom t
        else pure []

search :: Int -> IntMap IntSet -> IntSet
search = IM.findWithDefault IS.empty
