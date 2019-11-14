{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'HApply' and related instances via @TemplateHaskell@

module Hyper.TH.Apply
    ( makeHApply
    , makeHApplyAndBases
    , makeHApplicativeBases
    ) where

import           Control.Applicative (liftA2)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           GHC.Generics ((:*:)(..))
import           Hyper.Class.Apply
import           Hyper.TH.Functor (makeHFunctor)
import           Hyper.TH.Internal.Utils
import           Hyper.TH.Nodes (makeHNodes)
import           Hyper.TH.Pointed (makeHPointed)
import           Language.Haskell.TH

import           Prelude.Compat

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
        instanceD (simplifyContext (makeContext info)) (appT (conT ''HApply) (pure (tiInstance info)))
            [ InlineP 'hzip Inline FunLike AllPhases & PragmaD & pure
            , funD 'hzip
                [ Clause
                    [ consPat name xVars
                    , consPat name yVars
                    ] (NormalB (foldl AppE (ConE name) (zipWith f xVars yVars))) []
                    & pure
                ]
            ]
            <&> (:[])
    where
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = VarE '(<>)
        bodyForPat Node{} = ConE '(:*:)
        bodyForPat GenEmbed{} = VarE 'hzip
        bodyForPat FlatEmbed{} = VarE 'hzip
        bodyForPat (InContainer _ pat) = VarE 'liftA2 `AppE` bodyForPat pat
        f (p, x) (_, y) =
            bodyFor p `AppE` VarE x `AppE` VarE y

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info >>= (^. Lens._3) >>= ctxFor
    where
        ctxFor (Right x) = ctxForPat x
        ctxFor (Left x) = [ConT ''Semigroup `AppT` x]
        ctxForPat (InContainer t pat) = (ConT ''Applicative `AppT` t) : ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''HApply `AppT` t]
        ctxForPat (FlatEmbed t) = [ConT ''HApply `AppT` tiInstance t]
        ctxForPat _ = []
