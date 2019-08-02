{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Traversable
    ( makeKTraversable
    , makeKTraversableAndFoldable
    , makeKTraversableAndBases
    ) where

import           AST.Class.Traversable
import           AST.TH.Foldable (makeKFoldable)
import           AST.TH.Functor (makeKFunctor)
import           AST.TH.Internal
import           Control.Lens.Operators
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKTraversableAndBases :: Name -> DecsQ
makeKTraversableAndBases x =
    sequenceA
    [ makeKFunctor x
    , makeKTraversableAndFoldable x
    ] <&> concat

makeKTraversableAndFoldable :: Name -> DecsQ
makeKTraversableAndFoldable x =
    sequenceA
    [ makeKFoldable x
    , makeKTraversable x
    ] <&> concat

makeKTraversable :: Name -> DecsQ
makeKTraversable typeName = makeTypeInfo typeName >>= makeKTraversableForType

makeKTraversableForType :: TypeInfo -> DecsQ
makeKTraversableForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KTraversable) (pure (tiInstance info)))
    [ InlineP 'sequenceC Inline FunLike AllPhases & PragmaD & pure
    , funD 'sequenceC (tiCons info <&> pure . makeCons (tiVar info))
    ]
    <&> (:[])

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (Tof t pat) = (ConT ''Traversable `AppT` t) : ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KTraversable `AppT` t]
        ctxForPat _ = []

makeCons ::
    Name -> D.ConstructorInfo -> Clause
makeCons knot cons =
    Clause [consPat cons consVars] body []
    where
        body =
            consVars <&> f
            & applicativeStyle (ConE (D.constructorName cons))
            & NormalB
        consVars = makeConstructorVars "x" cons
        f (typ, name) = bodyForPat (matchType knot typ) `AppE` VarE name
        bodyForPat NodeFofX{} = VarE 'runContainedK
        bodyForPat XofF{} = VarE 'sequenceC
        bodyForPat (Tof _ pat) = VarE 'traverse `AppE` bodyForPat pat
        bodyForPat Other{} = VarE 'pure
