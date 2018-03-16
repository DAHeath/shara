module Grammar.Simplify where

import           Control.Lens
import           Control.Monad.State

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Foldable (foldrM)

import           Formula hiding (Rule)

import           Grammar.Grammar

simplify :: Grammar -> Grammar
simplify g =
  (g & grammarRules %~ clear) & grammarRules . traverse %~ (cleanUp . inlR)
  where
    -- Remove rules for nonterminals which we're going to inline.
    clear :: [Rule] -> [Rule]
    clear =
      filter ((`M.notMember` inmap) . view (ruleLHS . nonterminalSymbol))

    -- Rewrite a rule by inlining the rhs.
    inlR :: Rule -> Rule
    inlR r@(Rule lhs phi rhs) =
      foldr inlR' r rhs

    inlR' :: Nonterminal -> Rule -> Rule
    inlR' nt r@(Rule lhs phi rhs) =
      case M.lookup (view nonterminalSymbol nt) inmap of
        Nothing -> r
        Just (nts, phi') ->
          foldr inlR'
            (Rule lhs (phi `mkAnd` phi')
              (filter (/= nt) rhs ++ nts))
            nts

    inmap = inlineMap g

    cleanUp (Rule lhs phi rhs) =
      Rule lhs (varElim (varSet lhs `S.union` varSet rhs) phi) rhs

data InlineMode
  = OneRHS
  | Disallowed

-- | Construct a map by which to replace nonterminals. The map in the state
-- decides whether or not a symbol may be inlined.
inlineMap :: Grammar -> Map Symbol ([Nonterminal], Expr)
inlineMap g =
  let disMap = foldr (`M.insert` Disallowed) M.empty S.empty
      (inlines, modes) = runState (foldrM go M.empty (view grammarRules g)) disMap
  in
  M.filterWithKey (\k _ -> k `M.member` modes) inlines
  where
    go (Rule lhs phi rhs) m = do
      let lSym = view nonterminalSymbol lhs
      allow <- get
      -- First we will look at the lhs symbol and attempt to give it an inline
      -- definition.
      m' <- case (M.lookup lSym allow, M.lookup lSym m, rhs) of
        (Nothing, Nothing, [_]) ->
          -- There is no match for this symbol so far, so it is a candidate for
          -- inlining.
          pure (M.insert lSym (rhs, phi) m)
        (Just OneRHS, Nothing, [_]) ->
          -- This symbol has only appeared on the rhs once and has no lhs
          -- appearance yet, so add it as a candidate.
          pure (M.insert lSym (rhs, phi) m)
        (_, _, _) ->
          -- Other scenarios mean one of the following:
          --   The symbol has already appeared on the lhs.
          --   The symbol was already disallowed.
          -- These cases mean the symbol cannot be inlined.
          disallow lSym m

      -- Next, we will rule out symbols which have appeared too many times on
      -- the rhs.
      m'' <- foldrM (\nt sMap -> do
        let rSym = view nonterminalSymbol nt
        allow' <- get
        case M.lookup rSym allow' of
          Nothing -> do
            -- The symbol hasn't appeared on the rhs yet, so indicate it has
            -- appeared once.
            modify (M.insert rSym OneRHS)
            pure sMap
          _ ->
            -- The symbol has already appeared at least once on the rhs, so
            -- make sure it is not allowed to inline.
            disallow rSym sMap) m' rhs
      pure m''

    disallow sym m = do
      modify (M.insert sym Disallowed)
      pure (M.delete sym m)
