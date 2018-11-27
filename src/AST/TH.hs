{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.TH
    ( makeChildren, makeZipMatch
    ) where

import           AST (Node, Children(..))
import           AST.ZipMatch (ZipMatch(..))
import           Control.Lens.Operators
import           Control.Monad.Error.Class (MonadError(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeChildren :: Name -> DecsQ
makeChildren typeName =
    do
        info <- D.reifyDatatype typeName
        var <- getVar info
        childrenT <- childrenTypesFromTypeInfo info
        let childrenConstraint =
                Set.toList childrenT
                <&> ConT
                <&> AppT (VarT constraint)
                & foldl AppT (TupleT (Set.size childrenT))
        instanceD (pure []) (appT (conT ''Children) (conT typeName))
            [ tySynInstD ''ChildrenConstraint
                (pure (TySynEqn [ConT typeName, VarT constraint] childrenConstraint))
            , funD 'children (D.datatypeCons info <&> pure . makeChildrenCtr var)
            ]
            <&> (:[])
    where
        constraint = mkName "constraint"

getVar :: D.DatatypeInfo -> Q Name
getVar info =
    case D.datatypeVars info of
    [SigT (VarT var) _] -> pure var
    _ -> fail "unexpected number of type variables"

childrenTypesFromTypeInfo :: D.DatatypeInfo -> Q (Set Name)
childrenTypesFromTypeInfo info =
    do
        var <- getVar info
        D.datatypeCons info >>= D.constructorFields
            & traverse (childrenTypes var)
            <&> mconcat

childrenTypes :: Name -> Type -> Q (Set Name)
childrenTypes var (ConT node `AppT` VarT functor `AppT` ConT ast)
    | node == ''Node && functor == var = Set.singleton ast & pure
childrenTypes var (ConT ast `AppT` VarT functor)
    | functor == var = D.reifyDatatype ast >>= childrenTypesFromTypeInfo
childrenTypes _ _ = pure mempty

makeChildrenCtr :: Name -> D.ConstructorInfo -> Clause
makeChildrenCtr var info =
    Clause
    [VarP proxy, VarP func, ConP (D.constructorName info) (cVars <&> VarP)]
    (NormalB body) []
    where
        proxy = mkName "_p"
        func = mkName "_f"
        cVars =
            [0::Int ..] <&> show <&> ('x':) <&> mkName
            & take (length (D.constructorFields info))
        body =
            zipWith field cVars (D.constructorFields info)
            & applicativeStyle (ConE (D.constructorName info))
        field name (ConT node `AppT` VarT functor `AppT` ConT _)
            | node == ''Node && functor == var =
                AppE (VarE func) (VarE name)
        field name (ConT _ `AppT` VarT functor)
            | functor == var =
                VarE 'children `AppE` VarE proxy `AppE` VarE func `AppE` VarE name
        field name _ = AppE (VarE 'pure) (VarE name)

applicativeStyle :: Exp -> [Exp] -> Exp
applicativeStyle f =
    foldl ap (AppE (VarE 'pure) f)
    where
        ap x y = InfixE (Just x) (VarE '(<*>)) (Just y)

makeZipMatch :: Name -> DecsQ
makeZipMatch typeName =
    do
        info <- D.reifyDatatype typeName
        var <- getVar info
        instanceD (pure []) (appT (conT ''ZipMatch) (conT typeName))
            [ funD 'zipMatch
                ( (D.datatypeCons info <&> pure . makeZipMatchCtr var)
                    ++ [pure tailClause]
                )
            ]
            <&> (:[])
    where
        tailClause =
            Clause [WildP, WildP, WildP, WildP]
            (NormalB (AppE (VarE 'throwError) (TupE [])))
            []


makeZipMatchCtr :: Name -> D.ConstructorInfo -> Clause
makeZipMatchCtr var info =
    Clause [VarP proxy, VarP func, con fst, con snd] body []
    where
        proxy = mkName "_p"
        func = mkName "_f"
        con f = ConP (D.constructorName info) (cVars <&> f <&> VarP)
        cVars =
            [0::Int ..] <&> show <&> (\n -> (mkName ('x':n), mkName ('y':n)))
            & take (length (D.constructorFields info))
        body
            | null checks = NormalB bodyExp
            | otherwise = GuardedB [(NormalG (foldl1 mkAnd checks), bodyExp)]
        checks = fieldParts >>= snd
        mkAnd x y = InfixE (Just x) (VarE '(&&)) (Just y)
        fieldParts = zipWith field cVars (D.constructorFields info)
        bodyExp =
            fieldParts <&> fst
            & applicativeStyle (ConE (D.constructorName info))
        field (x, y) (ConT node `AppT` VarT functor `AppT` ConT _)
            | node == ''Node && functor == var =
                (VarE func `AppE` VarE x `AppE` VarE y, [])
        field (x, y) (ConT _ `AppT` VarT functor)
            | functor == var =
                (VarE 'zipMatch `AppE` VarE proxy `AppE` VarE func `AppE` VarE x `AppE` VarE y, [])
        field (x, y) _ =
            ( AppE (VarE 'pure) (VarE x)
            , [InfixE (Just (VarE x)) (VarE '(==)) (Just (VarE y))]
            )
