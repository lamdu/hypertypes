{-# LANGUAGE TemplateHaskell #-}

-- | Generate 'HApply' and related instances via @TemplateHaskell@

module Hyper.TH.Apply
    ( makeHApply
    , makeHApplyAndBases
    , makeHApplicativeBases
    ) where

import           Control.Applicative (liftA2)
import qualified Control.Lens as Lens
import           Hyper.Class.Apply (HApply(..))
import           Hyper.TH.Functor (makeHFunctor)
import           Hyper.TH.Internal.Utils
import           Hyper.TH.Nodes (makeHNodes)
import           Hyper.TH.Pointed (makeHPointed)
import           Language.Haskell.TH

import           Hyper.Internal.Prelude

-- | Generate instances of 'HApply',
-- 'Hyper.Class.Functor.HFunctor', 'Hyper.Class.Pointed.HPointed' and 'Hyper.Class.Nodes.HNodes',
-- which together form 'HApplicative'.
makeHApplicativeBases :: Name -> DecsQ
makeHApplicativeBases x =
    sequenceA
    [ makeHPointed x
    , makeHApplyAndBases x
    ] <&> concat

-- | Generate an instance of 'HApply'
-- along with its bases 'Hyper.Class.Functor.HFunctor' and 'Hyper.Class.Nodes.HNodes'
makeHApplyAndBases :: Name -> DecsQ
makeHApplyAndBases x =
    sequenceA
    [ makeHNodes x
    , makeHFunctor x
    , makeHApply x
    ] <&> concat

-- | Generate an instance of 'HApply'
makeHApply :: Name -> DecsQ
makeHApply typeName = makeTypeInfo typeName >>= makeHApplyForType

makeHApplyForType :: TypeInfo -> DecsQ
makeHApplyForType info =
    do
        (name, _, fields) <-
            case tiConstructors info of
            [x] -> pure x
            _ -> fail "makeHApply only supports types with a single constructor"
        let xVars = makeConstructorVars "x" fields
        let yVars = makeConstructorVars "y" fields
        instanceD (makeContext info >>= simplifyContext) [t|HApply $(pure (tiInstance info))|]
            [ InlineP 'hzip Inline FunLike AllPhases & PragmaD & pure
            , funD 'hzip
                [ clause
                    [ consPat name xVars
                    , consPat name yVars
                    ] (normalB (foldl appE (conE name) (zipWith f xVars yVars))) []
                ]
            ]
            <&> (:[])
    where
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = [|(<>)|]
        bodyForPat Node{} = [|(:*:)|]
        bodyForPat GenEmbed{} = [|hzip|]
        bodyForPat FlatEmbed{} = [|hzip|]
        bodyForPat (InContainer _ pat) = [|liftA2 $(bodyForPat pat)|]
        f (p, x) (_, y) = [|$(bodyFor p) $(varE x) $(varE y)|]

makeContext :: TypeInfo -> Q [Pred]
makeContext info =
    tiConstructors info >>= (^. Lens._3) >>= ctxFor & sequenceA
    where
        ctxFor (Right x) = ctxForPat x
        ctxFor (Left x) = [[t|Semigroup $(pure x)|]]
        ctxForPat (InContainer t pat) = [t|Applicative $(pure t)|] : ctxForPat pat
        ctxForPat (GenEmbed t) = [[t|HApply $(pure t)|]]
        ctxForPat (FlatEmbed t) = [[t|HApply $(pure (tiInstance t))|]]
        ctxForPat _ = []
