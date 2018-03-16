module Grammar.Shara.Cut where

import           Data.Set (Set)
import qualified Data.Set as S

import           Grammar.Grammar

cut :: Grammar -> Set Symbol -> (Set Symbol, Set Symbol, Set Symbol)
cut _ ss =
  -- TODO this is the trivial definition
  (ss, S.empty, S.empty)

