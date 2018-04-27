{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Shara.CDD where

import           Control.Lens
import           Control.Monad.State
import           Data.Data           (Data)
import           Data.Map            (Map)
import qualified Data.Map            as M
import           Data.Set            (Set)
import qualified Data.Set            as S
import           Formula
import           Prelude             hiding (seq)
import           Shara.Grammar
import           Shara.Inf
import qualified Shara.Reg           as R

import Debug.Trace

type Branch = Int
type Unrolling = Int

data CDDState = CDDState
  -- Which nonterminals have been seen in the current unrolling?
  { _visited :: Set NT
  -- Tracks the highest branch point thus far.
  , _branchCount :: Branch
  -- What is the identity of the current branch point?
  , _currentBranch :: Branch
  -- Which nonterminals is each branch point directly dependent on?
  , _branchDeps :: Map Branch (Set NT)
  -- Which branch points are siblings of a given branch point?
  , _branchSibs :: Map Branch (Set Branch)
  -- Which branch points are parents of a given branch point?
  , _branchPars :: Map Branch (Set Branch)
  -- Which branches are local to the given nonterminal?
  , _ntBranches :: Map NT (Set Branch)
  -- Tracks the highest variable count thus far.
  , _vocabCount :: Int
  -- What is the vocabulary of the given nonterminal?
  , _vocabulary :: Map NT [Var]
  -- What are the nonterminals that represent the given location?
  , _clones :: Map Unrolling (Map NT (Set NT))
  -- Tracks the highest fresh nonterminal thus far.
  , _ntCount :: Int
  -- Which nonterminal are we looking at? Note, we use 0 for S
  , _currentNT :: Int
  -- Which unrolling are we currently doing?
  , _currentUnrolling :: Unrolling
  } deriving (Show, Read, Eq, Ord)
makeLenses ''CDDState

-- | Given the vocabulary for the nonterminals in the original grammar,
-- generate a fresh CDD state.
emptyCDDState :: Map NT [Var] -> CDDState
emptyCDDState vocab = CDDState
  { _visited = S.empty
  , _branchCount = 0
  , _currentBranch = 0
  , _branchDeps = M.empty
  , _branchSibs = M.empty
  , _branchPars = M.empty
  , _ntBranches = M.empty
  , _vocabCount = 0
  , _vocabulary = vocab
  , _clones = M.empty
  , _ntCount = 0
  , _currentNT = 0
  , _currentUnrolling = 0
  }

unrollCDD :: MonadState CDDState m => IGrammar m Expr -> m (IGrammar m Expr)
unrollCDD g = do
  currentUnrolling += 1
  unroll g

finitePrefix :: IGrammar m Expr -> Grammar Expr
finitePrefix = finite (SGrammar R.Null M.empty)

cdd ::
     forall m. MonadState CDDState m
  => SGrammar [Var] Expr
  -> m (IGrammar m Expr)
cdd g = currentBranch .= 0 >> cddRule (start g & allFresh 0)
  where
    cddRule :: SRule [Var] Expr -> m (IGrammar m Expr)
    cddRule =
      \case
        R.Eps -> pure (iflat R.Eps)
        R.Null -> pure (iflat R.Null)
        R.Seq a b ->
          Infinite <$>
          (seq <$> (getInfinite <$> cddRule a) <*> (getInfinite <$> cddRule b))
        STerm t -> pure (iflat $ Term (Fin t))
        R.Alt a b -> do
          -- We need to invent 2 new branch points, one for each branch
          cb <- use currentBranch
          a' <- mkBranch cb >> getInfinite <$> cddRule a
          b' <- mkBranch cb >> getInfinite <$> cddRule b
          pure (Infinite (alt a' b'))
        SNonterm (vs, nt) ->
          -- | If the nonterminal has not been visited, visit it now.
          -- Also, manage the dependencies
          elem nt <$> use visited >>= \case
            -- We have alrady seen this nonterminal, so postpone expanding it.
            True ->
              pure (
                iflat $ Term (Inf (do
                visited .= S.empty
                cddRule (SNonterm (vs, nt)))))
            False -> do
              -- We have not yet seen this nonterminal, so mark it.
              cb <- use currentBranch
              -- Create a fresh nonterminal if needed, or use one we do not
              -- already depend on.
              ds <- deps cb
              cu <- use currentUnrolling
              cs <- findSet nt <$> (M.findWithDefault M.empty cu <$> use clones)
              case S.minView (cs S.\\ ds) of
                Just (nt', _) -> do
                  addDep cb nt'
                  vocab <- substMap vs nt nt'
                  pure (iflat (Term (Fin vocab) `R.seq` Nonterm nt'))
                Nothing -> do
                  nt' <- freshNT nt
                  addDep cb nt'
                  vocab <- substMap vs nt nt'
                  visited %= S.insert nt
                  g' <- getInfinite <$> cddRule (ruleFor nt g & allFresh nt')
                  visited %= S.delete nt
                  pure $ Infinite $ (flat (Term (Fin vocab)) `seq` abstract () nt' g')

mkBranch :: MonadState CDDState m => Branch -> m ()
mkBranch parent = do
  bc <- branchCount <+= 1
  branchPars . at bc <>= Just (S.singleton parent)
  branchSibs . at parent <>= Just (S.singleton bc)
  currentBranch .= bc

-- | Find all nonterminal dependencies of the current location in the grammar.
deps :: MonadState CDDState m => Branch -> m (Set NT)
deps b = do
  bs <- connectedBranches b
  bds <- use branchDeps
  pure (foldMap (`findSet` bds) bs)

-- | Find all the branches connected to the current branch.
connectedBranches :: MonadState CDDState m => Branch -> m (Set Branch)
connectedBranches b = do
  sibs <- use branchSibs
  pars <- use branchPars
  pure (execState (goSib sibs b) S.empty
    `mappend` execState (goPar pars b) S.empty)
  where
    goSib sibs b' = elem b' <$> get >>= \case
      True -> pure ()
      False -> do
        modify (S.insert b')
        mapM_ (goSib sibs) (findSet b' sibs)
    goPar pars b' = elem b' <$> get >>= \case
      True -> pure ()
      False -> do
        modify (S.insert b')
        mapM_ (goPar pars) (findSet b' pars)

substMap :: MonadState CDDState m => [Var] -> NT -> NT -> m Expr
substMap vs nt nt' = do
  vs' <- M.findWithDefault [] nt <$> use vocabulary
  pure (copyVars vs (vs' & allFresh nt'))

-- | Construct a fresh clone for the given nonterminal.
freshNT :: MonadState CDDState m => NT -> m NT
freshNT nt = do
  nt' <- ntCount <+= 1
  cu <- use currentUnrolling
  clones . at cu %= (\case
    Nothing -> Just (M.singleton nt (S.singleton nt'))
    Just m -> Just (m & at nt <>~ Just (S.singleton nt')))
  pure nt'

-- | Connect a branch point to a nonterminal by connecting all branch points
-- below the nonterminal to the branch point and adding the branch point below
-- the nonterminal.
addDep :: MonadState CDDState m => Branch -> NT -> m ()
addDep b nt = do
  bs <- findSet nt <$> use ntBranches
  mapM_ (connect b) bs
  ntBranches . at nt <>= Just (S.singleton b)
  branchDeps . at b <>= Just (S.singleton nt)

-- | Connect two branches by adding them as neighbors.
connect :: MonadState CDDState m => Branch -> Branch -> m ()
connect a b = do
  branchSibs . at a <>= Just (S.singleton b)
  branchSibs . at b <>= Just (S.singleton a)

-- | Construct a variable whose name reflects the nonterminal it belongs to.
freshVar :: NT -> Var -> Var
freshVar nt (Var n t) = Var (n ++ "#" ++ show nt) t

allFresh :: Data a => NT -> a -> a
allFresh nt x = x & vars %~ freshVar nt

findSet :: Ord a => a -> Map a (Set b) -> Set b
findSet = M.findWithDefault S.empty

-- | Embed a single rule into an infinite grammar.
iflat ::
     SRule s (Either a (m (Infinite m (SGrammar s) a)))
  -> Infinite m (SGrammar s) a
iflat = Infinite . flat
