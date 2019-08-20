{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Traversable
    ( makeKTraversable
    , makeKTraversableAndFoldable
    , makeKTraversableAndBases
    , makeKTraversableApplyAndBases
    ) where

import           AST.Class.Traversable
import           AST.TH.Apply (makeKApplicativeBases)
import           AST.TH.Foldable (makeKFoldable)
import           AST.TH.Functor (makeKFunctor)
import           AST.TH.Internal
import           AST.TH.Nodes (makeKNodes)
import           Control.Lens.Operators
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKTraversableApplyAndBases :: Name -> DecsQ
makeKTraversableApplyAndBases x =
    sequenceA
    [ makeKApplicativeBases x
    , makeKTraversableAndFoldable x
    ] <&> concat

makeKTraversableAndBases :: Name -> DecsQ
makeKTraversableAndBases x =
    sequenceA
    [ makeKNodes x
    , makeKFunctor x
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
    [ InlineP 'sequenceK Inline FunLike AllPhases & PragmaD & pure
    , funD 'sequenceK (tiCons info <&> pure . makeCons (tiVar info))
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
        bodyForPat XofF{} = VarE 'sequenceK
        bodyForPat (Tof _ pat) = VarE 'traverse `AppE` bodyForPat pat
        bodyForPat Other{} = VarE 'pure
