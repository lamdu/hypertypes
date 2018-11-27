{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.TH
    ( makeChildren, makeZipMatch
    ) where

import           AST (Node, Children(..), ChildOf)
import           AST.ZipMatch (ZipMatch(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Error.Class (MonadError(..))
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeChildren :: Name -> DecsQ
makeChildren typeName =
    do
        info <- D.reifyDatatype typeName
        (dst, var) <- parts info
        childrenT <-
            evalStateT (childrenTypes var (AppT dst (VarT var))) mempty
        let childrenConstraint =
                Set.toList childrenT
                <&> AppT (VarT constraint)
                & foldl AppT (TupleT (Set.size childrenT))
        inst <-
            instanceD (pure []) (appT (conT ''Children) (pure dst))
            [ tySynInstD ''ChildrenConstraint
                (pure (TySynEqn [dst, VarT constraint] childrenConstraint))
            , funD 'children (D.datatypeCons info <&> pure . makeChildrenCtr var)
            ]
        mono <-
            case Set.toList childrenT of
            [x] ->
                tySynInstD ''ChildOf
                (pure (TySynEqn [dst] x))
                <&> (:[])
            _ -> pure []
        pure (inst : mono)
    where
        constraint = mkName "constraint"

parts :: D.DatatypeInfo -> Q (Type, Name)
parts info =
    case D.datatypeVars info of
    [] -> fail "expected type constructor which requires arguments"
    xs ->
        case last xs of
        SigT (VarT var) _ ->
            pure (foldl AppT (ConT (D.datatypeName info)) (init xs), var)
        _ -> fail "expected last argument to be variable"

childrenTypes ::
    Name -> Type -> StateT (Set Type) Q (Set Type)
childrenTypes var typ =
    do
        did <- gets (^. Lens.contains typ)
        if did
            then
                pure mempty
            else
                case typ of
                ConT node `AppT` VarT functor `AppT` ast
                    | node == ''Node && functor == var ->
                        Set.singleton ast & pure
                ast `AppT` VarT functor
                    | functor == var ->
                        go [] ast
                        where
                            go as (ConT name) = childrenTypesFromTypeName name as
                            go as (AppT x a) = go (a:as) x
                            go _ _ = pure mempty
                _ -> pure mempty

childrenTypesFromTypeName ::
    Name -> [Type] -> StateT (Set Type) Q (Set Type)
childrenTypesFromTypeName name args =
    do
        info <- D.reifyDatatype name & lift
        let substs =
                zip (D.datatypeVars info) args
                >>= filterVar
                & Map.fromList
        (_, var) <- parts info & lift
        D.datatypeCons info >>= D.constructorFields
            <&> substitute substs
            & traverse (childrenTypes var)
            <&> mconcat
    where
        filterVar (VarT n, x) = [(n, x)]
        filterVar (SigT t _, x) = filterVar (t, x)
        filterVar _ = []

substitute :: Map Name Type -> Type -> Type
substitute s (ForallT b c t) = substitute s t & ForallT b c
substitute s (AppT f a) = AppT (substitute s f) (substitute s a)
substitute s (SigT t k) = SigT (substitute s t) k
substitute s (VarT n) = s ^. Lens.at n & fromMaybe (VarT n)
substitute s (InfixT l n r) = InfixT (substitute s l) n (substitute s r)
substitute s (UInfixT l n r) = UInfixT (substitute s l) n (substitute s r)
substitute s (ParensT t) = substitute s t & ParensT
substitute _ x = x

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
        field name (ConT node `AppT` VarT functor `AppT` _)
            | node == ''Node && functor == var =
                AppE (VarE func) (VarE name)
        field name (_ `AppT` VarT functor)
            | functor == var =
                VarE 'children `AppE` VarE proxy `AppE` VarE func `AppE` VarE name
        field name (AppT _ (ConT node `AppT` VarT functor `AppT` ConT _))
            | node == ''Node && functor == var =
                VarE 'traverse `AppE` VarE func `AppE` VarE name
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
        (dst, var) <- parts info
        instanceD (pure []) (appT (conT ''ZipMatch) (pure dst))
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
        field (x, y) (ConT node `AppT` VarT functor `AppT` _)
            | node == ''Node && functor == var =
                (VarE func `AppE` VarE x `AppE` VarE y, [])
        field (x, y) (_ `AppT` VarT functor)
            | functor == var =
                (VarE 'zipMatch `AppE` VarE proxy `AppE` VarE func `AppE` VarE x `AppE` VarE y, [])
        field (x, y) _ =
            ( AppE (VarE 'pure) (VarE x)
            , [InfixE (Just (VarE x)) (VarE '(==)) (Just (VarE y))]
            )
