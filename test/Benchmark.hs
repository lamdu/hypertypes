import AST
import AST.Unify
import Control.Exception (evaluate)
import Control.Lens.Operators
import Criterion (Benchmarkable, whnfIO)
import Criterion.Main (bench, defaultMain)
import LangB
import Text.PrettyPrint.HughesPJClass (prettyShow)
import TypeLang.Pure

fields :: [(String, Tree Pure Typ)]
fields = [ ("a" ++ show i, _Pure # TInt) | i <- [0 :: Int .. 100] ]

recordFwd :: Tree Pure Typ
recordFwd = record fields

recordBwd :: Tree Pure Typ
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
