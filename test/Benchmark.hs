import Control.Exception (evaluate)
import Control.Lens.Operators
import Criterion (Benchmarkable, whnfIO)
import Criterion.Main (bench, defaultMain)
import Hyper
import Hyper.Unify
import Hyper.Unify.New (unfreeze)
import LangB
import Text.PrettyPrint.HughesPJClass (prettyShow)
import TypeLang

import Prelude

fields :: [String]
fields = [ 'a' : show i | i <- [0 :: Int .. 100] ]

record :: [String] -> Pure # Typ
record = (^. hPlain) . TRecP . foldr (\k -> RExtendP (Name k) TIntP) REmptyP

recordFwd :: Pure # Typ
recordFwd = record fields

recordBwd :: Pure # Typ
recordBwd = record (reverse fields)

unifyLargeRows :: Benchmarkable
unifyLargeRows =
    do
        r1 <- unfreeze recordFwd
        r2 <- unfreeze recordBwd
        unify r1 r2
        & execPureInferB
        & either (fail . prettyShow) evaluate
        & whnfIO

main :: IO ()
main = defaultMain [bench "Unify large rows" unifyLargeRows]
