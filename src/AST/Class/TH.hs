{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Class.TH
    ( makeChildrenAndZipMatch
    , makeChildren, makeZipMatch
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Children.Mono (ChildOf)
import           AST.Class.Recursive (Recursive)
import           AST.Class.ZipMatch (ZipMatch(..))
import           AST.Node (Node, LeafNode)
import           Control.Applicative (liftA2)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..), evalStateT, gets, modify)
import           Data.Functor.Const (Const)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Language.Haskell.TH
import           Language.Haskell.TH.Subst (substitute)
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeChildrenAndZipMatch :: [Name] -> DecsQ
makeChildrenAndZipMatch typeNames =
    (<>)
    <$> makeChildren typeNames
    <*> (traverse makeZipMatch typeNames <&> concat)

makeChildren :: [Name] -> DecsQ
makeChildren typeNames =
    do
        typeInfos <- traverse makeTypeInfo typeNames
        (<>)
            <$> (traverse makeChildrenForType typeInfos <&> concat)
            <*> traverse makeRecursiveChildren (findRecursives typeInfos)

findRecursives :: [TypeInfo] -> [TypeInfo]
findRecursives infos
    | (infos <&> tiInstance) == (next <&> tiInstance) = infos
    | otherwise = findRecursives next
    where
        next = filter hasDeps infos
        hasDeps = all (`Set.member` cur) . Set.toList . tiChildren
        cur = Set.fromList (infos <&> tiInstance)

makeRecursiveChildren :: TypeInfo -> DecQ
makeRecursiveChildren info =
    instanceD (pure []) (conT ''Recursive `appT` conT ''Children `appT` pure (tiInstance info)) []

data TypeInfo = TypeInfo
    { tiInstance :: Type
    , tiVar :: Name
    , tiChildren :: Set Type
    , tiCons :: [D.ConstructorInfo]
    }

makeTypeInfo :: Name -> Q TypeInfo
makeTypeInfo name =
    do
        info <- D.reifyDatatype name
        (dst, var) <- parts info
        childs <- evalStateT (childrenTypes var (AppT dst (VarT var))) mempty
        pure TypeInfo
            { tiInstance = dst
            , tiVar = var
            , tiChildren = childs
            , tiCons = D.datatypeCons info
            }

makeChildrenForType :: TypeInfo -> DecsQ
makeChildrenForType info =
    do
        inst <-
            instanceD (pure []) (appT (conT ''Children) (pure (tiInstance info)))
            [ tySynInstD ''SubTreeConstraint
                (pure (TySynEqn [tiInstance info, VarT knot, VarT constraint] subTreeConstraint))
            , tySynInstD ''ChildrenConstraint
                (pure (TySynEqn [tiInstance info, VarT constraint] childrenConstraint))
            , funD 'children (tiCons info <&> pure . makeChildrenCtr (tiVar info))
            ]
        mono <-
            case Set.toList (tiChildren info) of
            [x] ->
                tySynInstD ''ChildOf
                (pure (TySynEqn [tiInstance info] x))
                <&> (:[])
            _ -> pure []
        pure (inst : mono)
    where
        constraint = mkName "constraint"
        knot = mkName "k"
        childrenConstraint =
            Set.toList (tiChildren info)
            <&> AppT (VarT constraint)
            & foldl AppT (TupleT (Set.size (tiChildren info)))
        subTreeConstraint =
            Set.toList (tiChildren info)
            <&> (\x -> VarT constraint `AppT` (ConT ''Node `AppT` VarT knot `AppT` x))
            & foldl AppT (TupleT (Set.size (tiChildren info)))

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
            then pure mempty
            else modify (Lens.contains typ .~ True) *> add (matchType var typ)
    where
        add (NodeFofX ast) = Set.singleton ast & pure
        add (XofF ast) =
            go [] ast
            where
                go as (ConT name) = childrenTypesFromTypeName name as
                go as (AppT x a) = go (a:as) x
                go _ _ = pure mempty
        add (Tof pat) = add pat
        add Other{} = pure mempty

matchType :: Name -> Type -> CtrTypePattern
matchType var (ConT node `AppT` VarT functor `AppT` ast)
    | node == ''Node && functor == var =
        NodeFofX ast
matchType var (VarT f0 `AppT` (ast `AppT` VarT f1))
    | f0 == var && f1 == var =
        -- Node type synonym expanded
        NodeFofX ast
matchType var (ConT node `AppT` VarT functor `AppT` leaf)
    | node == ''LeafNode && functor == var =
        NodeFofX (AppT (ConT ''Const) leaf)
matchType var (ast `AppT` VarT functor)
    | functor == var =
        XofF ast
matchType var t@(AppT _ typ) =
    -- TODO: check if applied over a functor-kinded type.
    case matchType var typ of
    Other{} -> Other t
    pat -> Tof pat
matchType _ t = Other t

data CtrTypePattern
    = NodeFofX Type
    | XofF Type
    | Tof CtrTypePattern
    | Other Type

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
            zipWith AppE
            (D.constructorFields info <&> matchType var <&> forPat)
            (cVars <&> VarE)
            & applicativeStyle (ConE (D.constructorName info))
        forPat NodeFofX{} = VarE func
        forPat XofF{} = VarE 'children `AppE` VarE proxy `AppE` VarE func
        forPat (Tof pat) = VarE 'traverse `AppE` forPat pat
        forPat Other{} = VarE 'pure

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
        let ctrs = D.datatypeCons info <&> makeZipMatchCtr var
        instanceD
            (pure (ctrs >>= zmcContext & Set.fromList & Set.toList))
            (appT (conT ''ZipMatch) (pure dst))
            [ funD 'zipMatch
                ( (ctrs <&> pure . zmcClause) ++ [pure tailClause]
                )
            ]
            <&> (:[])
    where
        tailClause =
            Clause [WildP, WildP, WildP, WildP] (NormalB (ConE 'Nothing)) []

data ZipMatchCtr =
    ZipMatchCtr
    { zmcClause :: Clause
    , zmcContext :: [Pred]
    }

makeZipMatchCtr :: Name -> D.ConstructorInfo -> ZipMatchCtr
makeZipMatchCtr var info =
    ZipMatchCtr
    { zmcClause = Clause [VarP proxy, VarP func, con fst, con snd] body []
    , zmcContext = fieldParts >>= zmfContext
    }
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
        checks = fieldParts >>= zmfConds
        mkAnd x y = InfixE (Just x) (VarE '(&&)) (Just y)
        fieldParts = zipWith field cVars (D.constructorFields info <&> matchType var)
        bodyExp =
            applicativeStyle2
            (ConE 'Just `AppE` (VarE 'pure `AppE` ConE (D.constructorName info)))
            (fieldParts <&> zmfResult)
        field (x, y) NodeFofX{} =
            ZipMatchField
            { zmfResult = ConE 'Just `AppE` (VarE func `AppE` VarE x `AppE` VarE y)
            , zmfConds = []
            , zmfContext = []
            }
        field (x, y) (XofF t) =
            ZipMatchField
            { zmfResult = VarE 'zipMatch `AppE` VarE proxy `AppE` VarE func `AppE` VarE x `AppE` VarE y
            , zmfConds = []
            , zmfContext = [ConT ''ZipMatch `AppT` t]
            }
        field _ Tof{} = error "TODO"
        field (x, y) (Other t) =
            ZipMatchField
            { zmfResult = ConE 'Just `AppE` (VarE 'pure `AppE` VarE x)
            , zmfConds = [InfixE (Just (VarE x)) (VarE '(==)) (Just (VarE y))]
            , zmfContext = [ConT ''Eq `AppT` t]
            }

data ZipMatchField = ZipMatchField
    { zmfResult :: Exp
    , zmfConds :: [Exp]
    , zmfContext :: [Pred]
    }

applicativeStyle2 :: Exp -> [Exp] -> Exp
applicativeStyle2 =
    foldl ap2
    where
        ap2 x y = VarE 'liftA2 `AppE` VarE '(<*>) `AppE` x `AppE` y
