import Control.Exception (evaluate)
import Control.Lens.Operators
import Criterion (Benchmarkable, nf, whnfIO)
import Criterion.Main (bench, bgroup, defaultMain)
import Data.Functor.Identity
import Hyper
import Hyper.Recurse
import Hyper.Type.Functor
import Hyper.Type.Prune
import Hyper.Unify
import Hyper.Unify.New (unfreeze)
import LangB
import Text.PrettyPrint.HughesPJClass (prettyShow)
import TypeLang
import Prelude

fields :: [String]
fields = ['a' : show i | i <- [0 :: Int .. 100]]

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
main =
    defaultMain
        [ bench "Unify large rows" unifyLargeRows
        , bgroup
            "unwrapM"
            [ bench (show i) (nf (unwrapM (const (^. _F)) . gen) (10 ^ i))
            | i <- [1 :: Int, 4]
            ]
        ]

gen :: Int -> F Identity # Prune
gen 0 = _F # Identity Pruned
gen n = _F # Identity (Unpruned (gen (n - 1)))
