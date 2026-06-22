import qualified AlphaEqTest
import qualified BlameTest
import Control.Lens.Operators
import qualified LangATest
import qualified LangBTest
import qualified PlainTest
import PolyKindsTH ()
import Test.Tasty

import Prelude

main :: IO ()
main =
    testGroup
        "Tests"
        [ testGroup "infer" [LangATest.test, LangBTest.test]
        , AlphaEqTest.test
        , BlameTest.test
        , PlainTest.test
        ]
        & defaultMain
