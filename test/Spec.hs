import Control.Lens.Operators
import qualified PlainTest
import PolyKindsTH ()
import Test.Tasty

import Prelude

main :: IO ()
main =
    testGroup
        "Tests"
        [PlainTest.test]
        & defaultMain
