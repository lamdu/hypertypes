{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.TH
    ( makeChildren
    ) where

import           AST
import           Control.Lens.Operators
import           Data.Set (Set)
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeChildren :: Name -> DecsQ
makeChildren typeName =
    do
        info <- D.reifyDatatype typeName
        let [SigT (VarT var) _] = D.datatypeVars info
        childrenT <- childrenTypesFromTypeInfo info
        let childrenConstraint =
                Set.toList childrenT
                <&> ConT
                <&> AppT (VarT constraint)
                & foldl AppT (TupleT (Set.size childrenT))
        instanceD (pure []) (appT (conT ''Children) (conT typeName))
            [ tySynInstD ''ChildrenConstraint
                (pure (TySynEqn [ConT typeName, VarT constraint] childrenConstraint))
            , funD 'children (D.datatypeCons info <&> makeChildrenCtr var)
            ]
            <&> (:[])
    where
        constraint = mkName "constraint"

childrenTypesFromTypeInfo :: D.DatatypeInfo -> Q (Set Name)
childrenTypesFromTypeInfo info =
    D.datatypeCons info >>= D.constructorFields
    & traverse (childrenTypes var)
    <&> mconcat
    where
        [SigT (VarT var) _] = D.datatypeVars info

childrenTypes :: Name -> Type -> Q (Set Name)
childrenTypes var (ConT node `AppT` VarT functor `AppT` ConT ast)
    | node == ''Node && functor == var = Set.singleton ast & pure
childrenTypes var (ConT ast `AppT` VarT functor)
    | functor == var = D.reifyDatatype ast >>= childrenTypesFromTypeInfo
childrenTypes _ _ = pure mempty

makeChildrenCtr :: Name -> D.ConstructorInfo -> ClauseQ
makeChildrenCtr var info =
    Clause
    [VarP proxy, VarP func, ConP (D.constructorName info) (cVars <&> VarP)]
    (NormalB body) []
    & pure
    where
        proxy = mkName "_p"
        func = mkName "_f"
        cVars = take (length (D.constructorFields info)) xVars
        body =
            zipWith varClause cVars (D.constructorFields info)
            & foldl ap (AppE (VarE 'pure) (ConE (D.constructorName info)))
        ap x y = InfixE (Just x) (VarE '(<*>)) (Just y)
        varClause name (ConT node `AppT` VarT functor `AppT` ConT _)
            | node == ''Node && functor == var =
                AppE (VarE func) (VarE name)
        varClause name (ConT _ `AppT` VarT functor)
            | functor == var =
                VarE 'children `AppE` VarE proxy `AppE` VarE func `AppE` VarE name
        varClause name _ = AppE (VarE 'pure) (VarE name)

xVars :: [Name]
xVars = [0::Int ..] <&> show <&> ('x':) <&> mkName
