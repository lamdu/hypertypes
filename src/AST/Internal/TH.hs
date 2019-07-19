{-# LANGUAGE NoImplicitPrelude, LambdaCase, DerivingVia, TemplateHaskellQuotes #-}
{-# LANGUAGE DeriveGeneric, TypeFamilies #-}

-- Helpers for TemplateHaskell instance generators

module AST.Internal.TH
    ( -- Internals for use in TH for sub-classes
      TypeInfo(..), TypeContents(..), CtrTypePattern(..)
    , ChildrenTypesInfo(..)
    , makeTypeInfo, makeChildrenTypesInfo
    , parts, toTuple, matchType
    , applicativeStyle, unapply, getVar, makeConstructorVars
    , consPat, simplifyContext
    ) where

import           AST.Class.Pointed
import           AST.Knot (Knot(..), RunKnot, Tie, ChildrenTypesOf)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..), evalStateT, execStateT, gets, modify)
import           Data.Foldable (traverse_)
import qualified Data.Has as Has
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Generic.Data (Generically(..))
import           GHC.Generics (Generic)
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

data TypeInfo = TypeInfo
    { tiInstance :: Type
    , tiVar :: Name
    , tiContents :: TypeContents
    , tiCons :: [D.ConstructorInfo]
    } deriving Show

data TypeContents = TypeContents
    { tcChildren :: Set Type
    , tcEmbeds :: Set Type
    , tcOthers :: Set Type
    } deriving (Show, Generic)
    deriving (Semigroup, Monoid) via Generically TypeContents

makeTypeInfo :: Name -> Q TypeInfo
makeTypeInfo name =
    do
        info <- D.reifyDatatype name
        (dst, var) <- parts info
        contents <- evalStateT (childrenTypes ''KLiftConstraint var (AppT dst (VarT var))) mempty
        pure TypeInfo
            { tiInstance = dst
            , tiVar = var
            , tiContents = contents
            , tiCons = D.datatypeCons info
            }

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
    Name -> Name -> Type -> StateT (Set Type) Q TypeContents
childrenTypes fam var typ =
    do
        did <- gets (^. Lens.contains typ)
        if did
            then pure mempty
            else modify (Lens.contains typ .~ True) *> add (matchType var typ)
    where
        add (NodeFofX ast) = pure mempty { tcChildren = Set.singleton ast }
        add (XofF ast) =
            case unapply ast of
            (ConT name, as) -> childrenTypesFromTypeName fam name as
            (x@VarT{}, as) -> pure mempty { tcEmbeds = Set.singleton (foldl AppT x as) }
            _ -> pure mempty
        add (Tof _ pat) = add pat
        add Other{} = pure mempty

unapply :: Type -> (Type, [Type])
unapply =
    go []
    where
        go as (SigT x _) = go as x
        go as (AppT f a) = go (a:as) f
        go as x = (x, as)

matchType :: Name -> Type -> CtrTypePattern
matchType var (ConT runKnot `AppT` VarT k `AppT` (PromotedT knot `AppT` ast))
    | runKnot == ''RunKnot && knot == 'Knot && k == var =
        NodeFofX ast
matchType var (ConT tie `AppT` VarT k `AppT` ast)
    | tie == ''Tie && k == var =
        NodeFofX ast
matchType var (ast `AppT` VarT knot)
    | knot == var && ast /= ConT ''RunKnot =
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
    Name -> Name -> [Type] -> StateT (Set Type) Q TypeContents
childrenTypesFromTypeName fam name args =
    reifyInstances fam [typ, VarT constraintVar] & lift
    >>=
    \case
    [] ->
        do
            info <- D.reifyDatatype name & lift
            let substs =
                    zip (D.datatypeVars info) args
                    >>= filterVar
                    & Map.fromList
            (_, var) <- parts info & lift
            D.datatypeCons info >>= D.constructorFields
                <&> D.applySubstitution substs
                & traverse (childrenTypes fam var)
                <&> mconcat
    [TySynInstD ccI (TySynEqn [typI, VarT cI] x)]
        | ccI == fam ->
            case unapply typI of
            (ConT n1, argsI) | n1 == name ->
                case traverse getVar argsI of
                Nothing ->
                    error ("TODO: Support Children constraint of flexible instances " <> show typ)
                Just argNames ->
                    childrenTypesFromChildrenConstraint fam cI (D.applySubstitution substs x)
                    where
                        substs = zip argNames args & Map.fromList
            _ -> error ("ReifyInstances brought wrong typ: " <> show (name, typI))
    xs -> error ("Malformed ChildrenConstraint instance: " <> show xs)
    where
        filterVar (VarT n, x) = [(n, x)]
        filterVar (SigT t _, x) = filterVar (t, x)
        filterVar _ = []
        typ = foldl AppT (ConT name) args

getVar :: Type -> Maybe Name
getVar (VarT x) = Just x
getVar (SigT x _) = getVar x
getVar _ = Nothing

constraintVar :: Name
constraintVar = mkName "constraint"

childrenTypesFromChildrenConstraint ::
    Name -> Name -> Type -> StateT (Set Type) Q TypeContents
childrenTypesFromChildrenConstraint _ c0 c@(AppT (VarT c1) x)
    | c0 == c1 = pure mempty { tcChildren = Set.singleton x }
    | otherwise = error ("TODO: Unsupported ChildrenContraint " <> show c)
childrenTypesFromChildrenConstraint fam c0 constraints =
    case unapply constraints of
    (ConT cc1, [x, VarT c1])
        | cc1 == fam && c0 == c1 ->
            pure mempty { tcEmbeds = Set.singleton x }
    (TupleT{}, xs) ->
        traverse (childrenTypesFromChildrenConstraint fam c0) xs <&> mconcat
    _ -> pure mempty { tcOthers = Set.singleton (D.applySubstitution subst constraints) }
    where
        subst = mempty & Lens.at c0 ?~ VarT constraintVar

toTuple :: Foldable t => t Type -> Type
toTuple xs = foldl AppT (TupleT (length xs)) xs

applicativeStyle :: Exp -> [Exp] -> Exp
applicativeStyle f =
    foldl ap (AppE (VarE 'pure) f)
    where
        ap x y = InfixE (Just x) (VarE '(<*>)) (Just y)

makeConstructorVars :: String -> D.ConstructorInfo -> [(Type, Name)]
makeConstructorVars prefix cons =
    [0::Int ..] <&> show <&> (('_':prefix) <>) <&> mkName
    & zip (D.constructorFields cons)

getChildrenTypes :: Type -> Q Type
getChildrenTypes typ =
    reifyInstances ''ChildrenTypesOf [typ]
    >>=
    \case
    [] -> fail ("Expecting a ChildrenTypesOf instance for " <> show typ)
    [TySynInstD ccI (TySynEqn [typI] x)]
        | ccI == ''ChildrenTypesOf ->
            case unapply typI of
            (ConT n1, argsI) | ConT n1 == typeFun ->
                case traverse getVar argsI of
                Nothing ->
                    fail ("TODO: Support ChildrenTypesOf of flexible instances: " <> show typ)
                Just argNames ->
                    pure (D.applySubstitution substs x)
                    where
                        substs = zip argNames args & Map.fromList
            _ -> fail ("ReifyInstances brought wrong typ: " <> show typ)
    [_] -> fail ("Unsupported ChildrenTypesOf form for " <> show typ)
    _ -> fail ("Impossible! Several ChildrenTypesOf instances for " <> show typ)
    where
        (typeFun, args) = unapply typ

consPat :: D.ConstructorInfo -> [(Type, Name)] -> Pat
consPat cons vars =
    ConP (D.constructorName cons) (vars <&> snd <&> VarP)

data ChildrenTypesInfo = ChildrenTypesInfo
    { childrenTypesType :: Type
    , childrenTypesPat :: Pat
    , varsForChildTypes :: Map Type Name
    , getEmbedTypes :: Type -> Q Exp
    }

makeChildrenTypesInfo :: TypeInfo -> Q ChildrenTypesInfo
makeChildrenTypesInfo typeInfo =
    do
        typ <- getChildrenTypes (tiInstance typeInfo)
        let (con, args) = unapply typ
        typeName <-
            case con of
            ConT x -> pure x
            _ -> fail ("unsupported ChildrenTypesOf: " <> show typ)
        info <- D.reifyDatatype typeName
        vars <-
            case D.datatypeVars info <&> getVar & sequenceA of
            Nothing -> fail ("Unexpected type parameters for children types: " <> show (D.datatypeVars info))
            Just x -> pure x
        cons <-
            case D.datatypeCons info of
            [x] -> pure x
            _ -> fail ("ChildrenTypesOf with more than one constructor: " <> show typ)
        let consVars = makeConstructorVars "c" cons
        let subst = zip vars args & Map.fromList
        let varsForEmbedTypes =
                do
                    (t, name) <- consVars
                    x `AppT` VarT _knot <- [t]
                    ConT cto `AppT` c <- [D.applySubstitution subst x]
                    [(c, name) | cto == ''ChildrenTypesOf]
                & Map.fromList
        let varsForOtherEmbeds =
                (D.applySubstitution subst typ, wholeVar) :
                do
                    (t, name) <- consVars
                    [] <-
                        do
                            ConT tie `AppT` VarT _ `AppT` _ <- [t]
                            [() | tie == ''Tie]
                        & pure
                    x `AppT` VarT _knot <- [t]
                    let xSub = D.applySubstitution subst x
                    [] <-
                        do
                            ConT cto `AppT` _ <- [xSub]
                            [() | cto == ''ChildrenTypesOf]
                        & pure
                    [(xSub, name)]
                & Map.fromList
        let getEmbed embedType =
                case Map.lookup embedType varsForEmbedTypes of
                Just x -> VarE x & pure
                Nothing ->
                    getChildrenTypes embedType
                    <&> (`Map.lookup` varsForOtherEmbeds)
                    <&> maybe (VarE 'Has.getter `AppE` VarE wholeVar) VarE
        pure ChildrenTypesInfo
            { childrenTypesType = typ
            , childrenTypesPat = AsP wholeVar (consPat cons consVars)
            , varsForChildTypes =
                do
                    (t, name) <- consVars
                    ConT tie `AppT` VarT _knot `AppT` c <- [t]
                    [(D.applySubstitution subst c, name) | tie == ''Tie]
                & Map.fromList
            , getEmbedTypes = getEmbed
            }
    where
        wholeVar = mkName "_cs"

simplifyContext :: [Pred] -> CxtQ
simplifyContext preds =
    goPreds preds
    & (`execStateT` (mempty :: Set (Name, [Type]), mempty :: Set Pred))
    <&> snd
    <&> Set.toList
    where
        goPreds ps = ps <&> unapply & traverse_ go
        go (c, [VarT v]) =
            -- Work-around reifyInstances returning instances for type variables
            -- by not checking.
            yep c [VarT v]
        go (ConT c, xs) =
            Lens.use (Lens._1 . Lens.contains key)
            >>=
            \case
            True -> pure () -- already checked
            False ->
                do
                    Lens._1 . Lens.contains key .= True
                    reifyInstances c xs & lift
                        >>=
                        \case
                        [InstanceD _ context other _] ->
                            D.unifyTypes [foldl AppT (ConT c) xs, other] & lift
                            <&> (`D.applySubstitution` context)
                            >>= goPreds
                        _ -> yep (ConT c) xs
            where
                key = (c, xs)
        go (c, xs) = yep c xs
        yep c xs = Lens._2 . Lens.contains (foldl AppT c xs) .= True
