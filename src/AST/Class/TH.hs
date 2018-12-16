{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Class.TH
    ( makeChildrenAndZipMatch
    , makeChildren, makeZipMatch
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Children.Mono (ChildOf)
import           AST.Class.Recursive (Recursive)
import           AST.Class.ZipMatch (ZipMatch(..), Both(..))
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

makeChildrenAndZipMatch :: [Name] -> DecsQ
makeChildrenAndZipMatch typeNames =
    (<>)
    <$> makeChildren typeNames
    <*> (traverse makeZipMatch typeNames <&> concat)

makeChildren :: [Name] -> DecsQ
makeChildren typeNames =
    do
        typeInfos <- traverse makeTypeInfo typeNames
        chldrn <- traverse makeChildrenForType typeInfos
        let recCtx = chldrn >>= snd & Set.fromList & Set.toList
        traverse (makeRecursiveChildren recCtx) (findRecursives typeInfos)
            <&> ((chldrn >>= fst) <>)

findRecursives :: [TypeInfo] -> [TypeInfo]
findRecursives infos
    | (infos <&> tiInstance) == (next <&> tiInstance) = infos
    | otherwise = findRecursives next
    where
        next = filter hasDeps infos
        hasDeps = all (`Set.member` cur) . Set.toList . tiChildren
        cur = Set.fromList (infos <&> tiInstance)

makeRecursiveChildren :: [Pred] -> TypeInfo -> DecQ
makeRecursiveChildren ctx info =
    instanceD (pure ctx) (conT ''Recursive `appT` conT ''Children `appT` pure (tiInstance info)) []

data TypeInfo = TypeInfo
    { tiInstance :: Type
    , tiVar :: Name
    , tiChildren :: Set Type
    , tiCons :: [D.ConstructorInfo]
    }
    deriving Show

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

makeChildrenForType :: TypeInfo -> Q ([Dec], [Pred])
makeChildrenForType info =
    do
        inst <-
            instanceD (pure ctx) (appT (conT ''Children) (pure (tiInstance info)))
            [ tySynInstD ''SubTreeConstraint
                (pure (TySynEqn [tiInstance info, VarT knot, VarT constraint] subTreeConstraint))
            , tySynInstD ''ChildrenConstraint
                (pure (TySynEqn [tiInstance info, VarT constraint] childrenConstraint))
            , funD 'children (ctrs <&> pure . ccClause)
            ]
        mono <-
            case Set.toList (tiChildren info) of
            [x] ->
                tySynInstD ''ChildOf
                (pure (TySynEqn [tiInstance info] x))
                <&> (:[])
            _ -> pure []
        pure (inst : mono, ctx)
    where
        ctrs = tiCons info <&> makeChildrenCtr (tiVar info)
        ctx = ctrs >>= ccContext & Set.fromList & Set.toList
        constraint = mkName "constraint"
        knot = mkName "knot"
        childrenConstraint =
            Set.toList (tiChildren info)
            <&> AppT (VarT constraint)
            & foldl AppT (TupleT (Set.size (tiChildren info)))
        subTreeConstraint =
            Set.toList (tiChildren info)
            <&> (\x -> VarT constraint `AppT` (ConT ''Tie `AppT` VarT knot `AppT` x))
            & foldl AppT (TupleT (Set.size (tiChildren info)))

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
        ctxForPat _ = []

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
            (pure (ctrs >>= ccContext & Set.fromList & Set.toList))
            (appT (conT ''ZipMatch) (pure dst))
            [ funD 'zipMatch
                ( (ctrs <&> pure . ccClause) ++ [pure tailClause]
                )
            ]
            <&> (:[])
    where
        tailClause = Clause [WildP, WildP] (NormalB (ConE 'Nothing)) []

data CtrCase =
    CtrCase
    { ccClause :: Clause
    , ccContext :: [Pred]
    }

makeZipMatchCtr :: Name -> D.ConstructorInfo -> CtrCase
makeZipMatchCtr var info =
    CtrCase
    { ccClause = Clause [con fst, con snd] body []
    , ccContext = fieldParts >>= zmfContext
    }
    where
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
        bodyExp = applicativeStyle (ConE (D.constructorName info)) (fieldParts <&> zmfResult)
        field (x, y) NodeFofX{} =
            ZipMatchField
            { zmfResult = ConE 'Just `AppE` (ConE 'Both `AppE` VarE x `AppE` VarE y)
            , zmfConds = []
            , zmfContext = []
            }
        field (x, y) (XofF t) =
            ZipMatchField
            { zmfResult = VarE 'zipMatch `AppE` VarE x `AppE` VarE y
            , zmfConds = []
            , zmfContext = [ConT ''ZipMatch `AppT` t]
            }
        field _ Tof{} = error "TODO"
        field (x, y) (Other t) =
            ZipMatchField
            { zmfResult = ConE 'Just `AppE` VarE x
            , zmfConds = [InfixE (Just (VarE x)) (VarE '(==)) (Just (VarE y))]
            , zmfContext = [ConT ''Eq `AppT` t | isPolymorphic t]
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

data ZipMatchField = ZipMatchField
    { zmfResult :: Exp
    , zmfConds :: [Exp]
    , zmfContext :: [Pred]
    }
