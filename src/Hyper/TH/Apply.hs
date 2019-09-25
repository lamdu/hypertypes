{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KApply' and related instances via @TemplateHaskell@

module Hyper.TH.Apply
    ( makeKApply
    , makeKApplyAndBases
    , makeKApplicativeBases
    ) where

import           Hyper.Class.Apply
import           Hyper.TH.Functor (makeKFunctor)
import           Hyper.TH.Internal.Utils
import           Hyper.TH.Nodes (makeKNodes)
import           Hyper.TH.Pointed (makeKPointed)
import           Control.Applicative (liftA2)
import           Control.Lens.Operators
import           Data.Functor.Product.PolyKinds (Product(..))
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate instances of 'KApply',
-- 'Hyper.Class.Functor.KFunctor', 'Hyper.Class.Pointed.KPointed' and 'Hyper.Class.Nodes.KNodes',
-- which together form 'KApplicative'.
makeKApplicativeBases :: Name -> DecsQ
makeKApplicativeBases x =
    sequenceA
    [ makeKPointed x
    , makeKApplyAndBases x
    ] <&> concat

-- | Generate an instance of 'KApply'
-- along with its bases 'Hyper.Class.Functor.KFunctor' and 'Hyper.Class.Nodes.KNodes'
makeKApplyAndBases :: Name -> DecsQ
makeKApplyAndBases x =
    sequenceA
    [ makeKNodes x
    , makeKFunctor x
    , makeKApply x
    ] <&> concat

-- | Generate an instance of 'KApply'
makeKApply :: Name -> DecsQ
makeKApply typeName = makeTypeInfo typeName >>= makeKApplyForType

makeKApplyForType :: TypeInfo -> DecsQ
makeKApplyForType info =
    do
        (name, fields) <-
            case tiConstructors info of
            [x] -> pure x
            _ -> fail "makeKApply only supports types with a single constructor"
        let xVars = makeConstructorVars "x" fields
        let yVars = makeConstructorVars "y" fields
        instanceD (simplifyContext (makeContext info)) (appT (conT ''KApply) (pure (tiInstance info)))
            [ InlineP 'zipK Inline FunLike AllPhases & PragmaD & pure
            , funD 'zipK
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
        bodyForPat Node{} = ConE 'Pair
        bodyForPat GenEmbed{} = VarE 'zipK
        bodyForPat FlatEmbed{} = VarE 'zipK
        bodyForPat (InContainer _ pat) = VarE 'liftA2 `AppE` bodyForPat pat
        f (p, x) (_, y) =
            bodyFor p `AppE` VarE x `AppE` VarE y

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info >>= snd >>= ctxFor
    where
        ctxFor (Right x) = ctxForPat x
        ctxFor (Left x) = [ConT ''Semigroup `AppT` x]
        ctxForPat (InContainer t pat) = (ConT ''Applicative `AppT` t) : ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''KApply `AppT` t]
        ctxForPat (FlatEmbed t) = [ConT ''KApply `AppT` tiInstance t]
        ctxForPat _ = []
