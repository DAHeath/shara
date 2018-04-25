import Finite

import Test.Hspec
import Data.Proxy
import Prop

main :: IO ()
main = hspec $
  describe "regular expression" $ do
    let proxy = Proxy :: Proxy Fin
    monoid (Proxy :: Proxy (Fin Int))
    alternative proxy
    monad proxy
