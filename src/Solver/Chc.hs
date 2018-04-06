module Solver.Chc where

import Data.Grammar
import Data.Semigroup

import Formula.Expr
import Formula.Var

-- | A fragment of a constrained Horn Clause rule.
data Fragment
  = Capture Var
  | Uncapture
  | Apply Var
  | Fact Expr
  deriving (Show, Read, Eq, Ord)

type Chc = Grammar Fragment

scope :: Var -> Rule Fragment -> Rule Fragment
scope v r = Terminal (Capture v) <> r <> Terminal Uncapture
