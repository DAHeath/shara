{-# LANGUAGE TemplateHaskell #-}
module Grammar.Shara.Test where

import           Control.Lens hiding (mapping)
import           Control.Monad.State

import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

import           Formula hiding (Rule)
import           Grammar.Grammar
import           Grammar.Graph

data Vertex = Vertex Int [Var] [Edge]

data Edge = Edge [Vertex] Rule

test :: IO ()
test = do
  let newVertex = 