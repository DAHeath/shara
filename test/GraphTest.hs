import Graph

import Test.Hspec
import Data.Proxy
import Prop

main :: IO ()
main = hspec $
  describe "graph" $ do
    let proxy = Proxy :: Proxy Graph
    monoid (Proxy :: Proxy (Graph Int))
    -- alternative proxy
    monad proxy
