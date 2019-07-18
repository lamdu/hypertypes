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
makeKPointed typeName = makeTypeInfo typeName >>= makeKPointedForType typeName

makeKPointedForType :: Name -> TypeInfo -> DecsQ
makeKPointedForType typeName info =
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
                | childrenTypes == tiInstance info =
                    Clause [] (NormalB (VarE 'id)) [] & pure
                | otherwise = makePureCCtr childrenTypes (tiVar info) cons
        instanceD (pure (makeContext info)) (appT (conT ''KPointed) (pure (tiInstance info)))
            [ tySynInstD ''KLiftConstraint
                (pure (TySynEqn [tiInstance info, VarT constraintVar] liftedConstraint))
            , InlineP 'pureC Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureC [pureCDecl]
            , InlineP 'pureK Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureK [makePureKCtr (tiVar info) cons]
            , InlineP 'pureKWith Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureKWith [makePureKWithCtr (tiVar info) cons]
            ]
    <&> (:[])
    where
        contents = tiContents info
        liftedConstraint =
            (Set.toList (tcChildren contents) <&> (VarT constraintVar `AppT`))
            <> (Set.toList (tcEmbeds contents) <&>
                \x -> ConT ''KLiftConstraint `AppT` x `AppT` VarT constraintVar)
            <> Set.toList (tcOthers contents)
            & toTuple
        (_, args) = unapply (tiInstance info)

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

makePureCCtr :: Type -> Name -> D.ConstructorInfo -> Q Clause
makePureCCtr childrenTypes knot info =
    do
        childrenTypeName <-
            case childrenCon of
            ConT x -> pure x
            _ -> fail ("unsupported ChildrenTypesOf: " <> show childrenTypes)
        childrenInfo <- D.reifyDatatype childrenTypeName
        childrenVars <-
            D.datatypeVars childrenInfo
            <&> getVar
            & sequenceA
            & maybe
                (fail ("pureC: unexpected type parameters for children types: " <> show (D.datatypeVars childrenInfo)))
                pure
        let childrenSubst = zip childrenVars childrenArgs & Map.fromList
        cons <-
            case D.datatypeCons childrenInfo of
            [x] -> pure x
            _ -> fail ("ChildrenTypesOf with more than one constructor: " <> show childrenTypeName)
        let cVars =
                [0::Int ..] <&> show <&> ('x':) <&> mkName
                & zip (D.constructorFields cons)
        let directChildVars =
                do
                    (typ, name) <- cVars
                    ConT tie `AppT` _ `AppT` c <- [typ]
                    [(D.applySubstitution childrenSubst c, name) | tie == ''Tie]
                & Map.fromList
        let bodyForPat (NodeFofX typ) =
                Map.lookup typ directChildVars
                & maybe (fail err) (pure . VarE)
                where
                    err =
                        "Failed producing pureC for child of type:\n        " <> show typ <>
                        "\n    not in:\n        " <> show directChildVars
            bodyForPat XofF{} = VarE 'pureC `AppE` LitE (StringL "TODO:makePureCCtr XofF") & pure
            bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'pure)
            bodyForPat (Other x) = fail ("KPointed can't produce value of type " <> show x)
        D.constructorFields info
            <&> matchType knot
            & traverse bodyForPat
            <&> foldl AppE (ConE (D.constructorName info))
            <&> NormalB
            <&> \x -> Clause [ConP (D.constructorName cons) (cVars <&> snd <&> VarP)] x []
    where
        (childrenCon, childrenArgs) = unapply childrenTypes
