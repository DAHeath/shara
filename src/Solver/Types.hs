{-# LANGUAGE TemplateHaskell #-}
module Solver.Types where

import           Control.Lens

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import           Data.Grammar (Grammar, Rule, NT)
import qualified Data.Grammar as G

type ProofStructure = Grammar Proof

data Proof = Continue | Entails NT NT
  deriving (Show, Read, Eq, Ord)

data DirectState = DirectState
