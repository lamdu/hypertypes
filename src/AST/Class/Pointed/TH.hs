{-# LANGUAGE NoImplicitPrelude, TemplateHaskellQuotes, LambdaCase #-}

module AST.Class.Pointed.TH
    ( makeKPointed
    ) where

import           AST.Knot
import           AST.Class.Pointed
import           AST.Internal.TH
import           Control.Lens.Operators
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKPointed :: Name -> DecsQ
makeKPointed typeName = makeTypeInfo typeName >>= makeKPointedForType

makeKPointedForType :: TypeInfo -> DecsQ
makeKPointedForType info =
    do
        childrenTypes <-
            reifyInstances ''ChildrenTypesOf [tiInstance info]
            >>=
            \case
            [] -> fail ("Expecting a ChildrenTypesOf instance for " <> show (tiInstance info))
            [TySynInstD ccI (TySynEqn [typI] x)]
                | ccI == ''ChildrenTypesOf ->
                    case unapply typI of
                    (ConT n1, argsI) | n1 == typeName ->
                        case traverse getVar argsI of
                        Nothing ->
                            fail ("TODO: Support ChildrenTypesOf of flexible instances: " <> show typeName)
                        Just argNames ->
                            pure (D.applySubstitution substs x)
                            where
                                substs = zip argNames args & Map.fromList
                    _ -> fail ("ReifyInstances brought wrong typ: " <> show typeName)
            [_] -> fail ("Unsupported ChildrenTypesOf form for " <> show (tiInstance info))
            _ -> fail ("Impossible! Several ChildrenTypesOf instances for " <> show (tiInstance info))
        cons <-
            case tiCons info of
            [x] -> pure x
            _ -> fail "makeKPointed only supports single constructor types"
        let pureCDecl
                | childrenTypes == tiInstance info = []
                | otherwise =
                    [ InlineP 'pureC Inline FunLike AllPhases & PragmaD & pure
                    , funD 'pureC [makePureCCtr (tiVar info) cons & pure]
                    ]
        [ tySynInstD ''KLiftConstraint
                (pure (TySynEqn [tiInstance info, VarT constraintVar] liftedConstraint))
            , InlineP 'pureK Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureK [makePureKCtr (tiVar info) cons]
            , InlineP 'pureKWith Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureKWith [makePureKWithCtr (tiVar info) cons]
            ] <> pureCDecl
            & instanceD (pure (makeContext info)) (appT (conT ''KPointed) (pure (tiInstance info)))
    <&> (:[])
    where
        contents = tiContents info
        liftedConstraint =
            (Set.toList (tcChildren contents) <&> (VarT constraintVar `AppT`))
            <> (Set.toList (tcEmbeds contents) <&>
                \x -> ConT ''KLiftConstraint `AppT` x `AppT` VarT constraintVar)
            <> Set.toList (tcOthers contents)
            & toTuple
        (typeNameFun, args) = unapply (tiInstance info)
        typeName =
            case typeNameFun of
            ConT x -> x
            _ -> error "unexpected type name"

constraintVar :: Name
constraintVar = mkName "constraint"

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (Tof t pat) = [ConT ''Applicative `AppT` t | isPolymorphic t] <> ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KPointed `AppT` t | isPolymorphic t]
        ctxForPat _ = []

varF :: Name
varF = mkName "_f"

makePureKCtr :: Name -> D.ConstructorInfo -> Q Clause
makePureKCtr knot info =
    D.constructorFields info
    <&> matchType knot
    & traverse bodyForPat
    <&> foldl AppE (ConE (D.constructorName info))
    <&> NormalB
    <&> \x -> Clause [VarP varF] x []
    where
        bodyForPat NodeFofX{} = VarE varF & pure
        bodyForPat XofF{} = VarE 'pureK `AppE` VarE varF & pure
        bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'pure)
        bodyForPat (Other x) = fail ("KPointed can't produce value of type " <> show x)

makePureKWithCtr :: Name -> D.ConstructorInfo -> Q Clause
makePureKWithCtr knot info =
    D.constructorFields info
    <&> matchType knot
    & traverse bodyForPat
    <&> foldl AppE (ConE (D.constructorName info))
    <&> NormalB
    <&> \x -> Clause [VarP proxy, VarP varF] x []
    where
        proxy = mkName "_p"
        bodyForPat NodeFofX{} = VarE varF & pure
        bodyForPat XofF{} = VarE 'pureKWith `AppE` VarE proxy `AppE` VarE varF & pure
        bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'pure)
        bodyForPat (Other x) = fail ("KPointed can't produce value of type " <> show x)

makePureCCtr :: Name -> D.ConstructorInfo -> Clause
makePureCCtr _ _ = Clause [] (NormalB (LitE (StringL "TODO:makePureCCtr"))) []
