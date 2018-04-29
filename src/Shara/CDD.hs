{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Shara.CDD where

import           Control.Lens
import           Control.Monad.State
import           Data.Data                   (Data)
import           Data.IntMap                 (IntMap)
import qualified Data.IntMap                 as M
import           Data.IntSet                 (IntSet)
import qualified Data.IntSet                 as S
import           Data.Language.Grammar
import           Data.Language.Inf
import qualified Data.Language.Reg           as R
import qualified Data.Language.ScopedGrammar as SG
import           Formula
import           Prelude                     hiding (null, seq)

type Branch = Int

type Unrolling = Int

data CDDState = CDDState
  -- Which nonterminals have been seen in the current unrolling?
  { _visited          :: IntSet
  -- Tracks the highest branch point thus far.
  , _branchCount      :: Branch
  -- What is the identity of the current branch point?
  , _currentBranch    :: Branch
  -- Which nonterminals is each branch point directly dependent on?
  , _branchDeps       :: IntMap IntSet
  -- Which branch points are siblings of a given branch point?
  , _branchSibs       :: IntMap IntSet
  -- Which branch points are parents of a given branch point?
  , _branchPars       :: IntMap IntSet
  -- Which branches are local to the given nonterminal?
  , _ntBranches       :: IntMap IntSet
  -- Tracks the highest variable count thus far.
  , _vocabCount       :: Int
  -- What is the vocabulary of the given nonterminal?
  , _vocabulary       :: IntMap [Var]
  -- What are the nonterminals that represent the given location?
  , _clones           :: IntMap (IntMap IntSet)
  -- Tracks the highest fresh nonterminal thus far.
  , _ntCount          :: Int
  -- Which nonterminal are we looking at? Note, we use 0 for S
  , _currentNT        :: Int
  -- Which unrolling are we currently doing?
  , _currentUnrolling :: Unrolling
  } deriving (Show, Read, Eq, Ord)

makeLenses ''CDDState

-- | Given the vocabulary for the nonterminals in the original grammar,
-- generate a fresh CDD state.
emptyCDDState :: IntMap [Var] -> CDDState
emptyCDDState vocab =
  CDDState
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
finitePrefix = finite null

cdd ::
     forall m. MonadState CDDState m
  => SG.Grammar [Var] Expr
  -> m (IGrammar m Expr)
cdd g = currentBranch .= 0 >> cddRule (SG.start g & allFresh 0)
  where
    cddRule :: SG.Rule [Var] Expr -> m (IGrammar m Expr)
    cddRule =
      \case
        R.Eps -> pure (iflat R.Eps)
        R.Null -> pure (iflat R.Null)
        R.Seq a b ->
          Infinite <$>
          (seq <$> (getInfinite <$> cddRule a) <*> (getInfinite <$> cddRule b))
        R.Alt a b
          -- We need to invent 2 new branch points, one for each branch
         -> do
          cb <- use currentBranch
          a' <- mkBranch cb >> getInfinite <$> cddRule a
          b' <- mkBranch cb >> getInfinite <$> cddRule b
          pure (Infinite (alt a' b'))
        SG.Term t -> pure (iflat $ Term (Fin t))
        SG.Nonterm vs nt
          -- | If the nonterminal has not been visited, visit it now.
          -- Also, manage the dependencies
         ->
          S.member nt <$> use visited >>=
            -- We have alrady seen this nonterminal, so postpone expanding it.
           \case
            True ->
              pure
                (iflat $
                 Term
                   (Inf
                      (do visited .= S.empty
                          cddRule (SG.Nonterm vs nt))))
            False
              -- We have not yet seen this nonterminal, so mark it.
             -> do
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
                  g' <- getInfinite <$> cddRule (SG.ruleFor nt g & allFresh nt')
                  visited %= S.delete nt
                  pure $
                    Infinite (flat (Term (Fin vocab)) `seq` abstract nt' g')

mkBranch :: MonadState CDDState m => Branch -> m ()
mkBranch parent = do
  bc <- branchCount <+= 1
  branchPars . at bc <>= Just (S.singleton parent)
  branchSibs . at parent <>= Just (S.singleton bc)
  currentBranch .= bc

-- | Find all nonterminal dependencies of the current location in the grammar.
deps :: MonadState CDDState m => Branch -> m IntSet
deps b = do
  bs <- connectedBranches b
  bds <- use branchDeps
  pure (foldMap (`findSet` bds) (S.toList bs))

-- | Find all the branches connected to the current branch.
connectedBranches :: MonadState CDDState m => Branch -> m IntSet
connectedBranches b = do
  sibs <- use branchSibs
  pars <- use branchPars
  pure
    (execState (goSib sibs b) S.empty `mappend` execState (goPar pars b) S.empty)
  where
    goSib sibs b' =
      gets (S.member b') >>= \case
        True -> pure ()
        False -> do
          modify (S.insert b')
          mapM_ (goSib sibs) (S.toList $ findSet b' sibs)
    goPar pars b' =
      gets (S.member b') >>= \case
        True -> pure ()
        False -> do
          modify (S.insert b')
          mapM_ (goPar pars) (S.toList $ findSet b' pars)

substMap :: MonadState CDDState m => [Var] -> NT -> NT -> m Expr
substMap vs nt nt' = do
  vs' <- M.findWithDefault [] nt <$> use vocabulary
  pure (copyVars vs (vs' & allFresh nt'))

-- | Construct a fresh clone for the given nonterminal.
freshNT :: MonadState CDDState m => NT -> m NT
freshNT nt = do
  nt' <- ntCount <+= 1
  cu <- use currentUnrolling
  clones . at cu %=
    (\case
       Nothing -> Just (M.singleton nt (S.singleton nt'))
       Just m -> Just (m & at nt <>~ Just (S.singleton nt')))
  pure nt'

-- | Connect a branch point to a nonterminal by connecting all branch points
-- below the nonterminal to the branch point and adding the branch point below
-- the nonterminal.
addDep :: MonadState CDDState m => Branch -> NT -> m ()
addDep br nt = do
  bs <- findSet nt <$> use ntBranches
  mapM_ (connect br) (S.toList bs)
  ntBranches . at nt <>= Just (S.singleton br)
  branchDeps . at br <>= Just (S.singleton nt)
  where
    connect a b = do
      branchSibs . at a <>= Just (S.singleton b)
      branchSibs . at b <>= Just (S.singleton a)

-- | Construct a variable whose name reflects the nonterminal it belongs to.
allFresh :: Data a => NT -> a -> a
allFresh nt x = x & vars %~ go
  where
    go (Var n t) = Var (n ++ "#" ++ show nt) t

findSet :: Int -> IntMap IntSet -> IntSet
findSet = M.findWithDefault S.empty

-- | Embed a single rule into an infinite grammar.
iflat :: Rule (Either (m (IGrammar m a)) a) -> IGrammar m a
iflat = Infinite . flat
