{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Class.Children.TH
    ( makeChildren
    , -- Internals for use in TH for sub-classes
      TypeInfo(..), CtrTypePattern(..), CtrCase(..)
    , parts, matchType, applicativeStyle, isPolymorphic, childrenContext, makeTypeInfo
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Children.Mono (ChildOf)
import           AST.Knot (Knot(..), RunKnot, Tie)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..), evalStateT, gets, modify)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeChildren :: Name -> DecsQ
makeChildren typeName = makeTypeInfo typeName >>= makeChildrenForType

data TypeInfo = TypeInfo
    { tiInstance :: Type
    , tiVar :: Name
    , tiChildren :: Set Type
    , tiEmbeds :: Set Type
    , tiCons :: [D.ConstructorInfo]
    }
    deriving Show

makeTypeInfo :: Name -> Q TypeInfo
makeTypeInfo name =
    do
        info <- D.reifyDatatype name
        (dst, var) <- parts info
        (childs, embeds) <- evalStateT (childrenTypes var (AppT dst (VarT var))) mempty
        pure TypeInfo
            { tiInstance = dst
            , tiVar = var
            , tiChildren = childs
            , tiEmbeds = embeds
            , tiCons = D.datatypeCons info
            }

makeChildrenForType :: TypeInfo -> DecsQ
makeChildrenForType info =
    do
        inst <-
            instanceD (pure ctx) (appT (conT ''Children) (pure (tiInstance info)))
            [ tySynInstD ''SubTreeConstraint
                (pure (TySynEqn [tiInstance info, VarT knot, VarT constraint] subTreeConstraint))
            , tySynInstD ''ChildrenConstraint
                (pure (TySynEqn [tiInstance info, VarT constraint] childrenConstraint))
            , funD 'children (tiCons info <&> pure . ccClause . makeChildrenCtr (tiVar info))
            ]
        mono <-
            case Set.toList (tiChildren info) of
            [x] ->
                tySynInstD ''ChildOf
                (pure (TySynEqn [tiInstance info] x))
                <&> (:[])
            _ -> pure []
        inst : mono & pure
    where
        ctx = childrenContext info
        constraint = mkName "constraint"
        knot = mkName "knot"
        childrenConstraint =
            (Set.toList (tiChildren info) <&> (VarT constraint `AppT`))
            <> (Set.toList (tiEmbeds info) <&>
                (\x -> ConT ''ChildrenConstraint `AppT` x `AppT` VarT constraint))
            & toTuple
        subTreeConstraint =
            (Set.toList (tiChildren info)
                <&> (\x -> ConT ''Tie `AppT` VarT knot `AppT` x))
            <> (Set.toList (tiEmbeds info) <&> (`AppT` VarT knot))
            <&> (VarT constraint `AppT`)
            & toTuple

toTuple :: Foldable t => t Type -> Type
toTuple xs = foldl AppT (TupleT (length xs)) xs

childrenContext :: TypeInfo -> [Pred]
childrenContext info =
    tiCons info <&> makeChildrenCtr (tiVar info) >>= ccContext & Set.fromList & Set.toList

parts :: D.DatatypeInfo -> Q (Type, Name)
parts info =
    case D.datatypeVars info of
    [] -> fail "expected type constructor which requires arguments"
    xs ->
        case last xs of
        SigT (VarT var) (ConT knot) | knot == ''Knot -> pure (res, var)
        VarT var -> pure (res, var)
        _ -> fail "expected last argument to be a knot variable"
        where
            res = foldl AppT (ConT (D.datatypeName info)) (init xs <&> stripSigT)
    where
        stripSigT (SigT x _) = x
        stripSigT x = x

childrenTypes ::
    Name -> Type -> StateT (Set Type) Q (Set Type, Set Type)
childrenTypes var typ =
    do
        did <- gets (^. Lens.contains typ)
        if did
            then pure mempty
            else modify (Lens.contains typ .~ True) *> add (matchType var typ)
    where
        add (NodeFofX ast) = pure (Set.singleton ast, mempty)
        add (XofF ast) =
            go [] ast
            where
                go as (ConT name) = childrenTypesFromTypeName name as
                go as (AppT x a) = go (a:as) x
                go as x@VarT{} = pure (mempty, Set.singleton (foldl AppT x as))
                go _ _ = pure mempty
        add (Tof _ pat) = add pat
        add Other{} = pure mempty

matchType :: Name -> Type -> CtrTypePattern
matchType var (ConT runKnot `AppT` VarT k `AppT` (PromotedT knot `AppT` ast))
    | runKnot == ''RunKnot && knot == 'Knot && k == var =
        NodeFofX ast
matchType var (ConT tie `AppT` VarT k `AppT` ast)
    | tie == ''Tie && k == var =
        NodeFofX ast
matchType var (ast `AppT` VarT knot)
    | knot == var =
        XofF ast
matchType var x@(AppT t typ) =
    -- TODO: check if applied over a functor-kinded type.
    case matchType var typ of
    Other{} -> Other x
    pat -> Tof t pat
matchType _ t = Other t

data CtrTypePattern
    = NodeFofX Type
    | XofF Type
    | Tof Type CtrTypePattern
    | Other Type
    deriving Show

childrenTypesFromTypeName ::
    Name -> [Type] -> StateT (Set Type) Q (Set Type, Set Type)
childrenTypesFromTypeName name args =
    do
        info <- D.reifyDatatype name & lift
        let substs =
                zip (D.datatypeVars info) args
                >>= filterVar
                & Map.fromList
        (_, var) <- parts info & lift
        D.datatypeCons info >>= D.constructorFields
            <&> D.applySubstitution substs
            & traverse (childrenTypes var)
            <&> mconcat
    where
        filterVar (VarT n, x) = [(n, x)]
        filterVar (SigT t _, x) = filterVar (t, x)
        filterVar _ = []

makeChildrenCtr :: Name -> D.ConstructorInfo -> CtrCase
makeChildrenCtr var info =
    CtrCase
    { ccClause =
        Clause
        [VarP proxy, VarP func, ConP (D.constructorName info) (cVars <&> VarP)]
        (NormalB body) []
    , ccContext = pats >>= ctxForPat
    }
    where
        proxy = mkName "_p"
        func = mkName "_f"
        cVars =
            [0::Int ..] <&> show <&> ('x':) <&> mkName
            & take (length (D.constructorFields info))
        body =
            zipWith AppE
            (pats <&> bodyForPat)
            (cVars <&> VarE)
            & applicativeStyle (ConE (D.constructorName info))
        pats = D.constructorFields info <&> matchType var
        bodyForPat NodeFofX{} = VarE func
        bodyForPat XofF{} = VarE 'children `AppE` VarE proxy `AppE` VarE func
        bodyForPat (Tof _ pat) = VarE 'traverse `AppE` bodyForPat pat
        bodyForPat Other{} = VarE 'pure
        ctxForPat (Tof t pat) = [ConT ''Traversable `AppT` t | isPolymorphic t] ++ ctxForPat pat
        ctxForPat (XofF t) = [ConT ''Children `AppT` t | isPolymorphic t]
        ctxForPat _ = []

applicativeStyle :: Exp -> [Exp] -> Exp
applicativeStyle f =
    foldl ap (AppE (VarE 'pure) f)
    where
        ap x y = InfixE (Just x) (VarE '(<*>)) (Just y)

data CtrCase =
    CtrCase
    { ccClause :: Clause
    , ccContext :: [Pred]
    }

isPolymorphic :: Type -> Bool
isPolymorphic VarT{} = True
isPolymorphic (AppT x y) = isPolymorphic x || isPolymorphic y
isPolymorphic (ParensT x) = isPolymorphic x
isPolymorphic ConT{} = False
isPolymorphic ArrowT{} = False
isPolymorphic ListT{} = False
isPolymorphic EqualityT{} = False
isPolymorphic TupleT{} = False
isPolymorphic UnboxedTupleT{} = False
isPolymorphic UnboxedSumT{} = False
isPolymorphic _ =
    -- TODO: Cover all cases
    True
