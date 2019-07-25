{-# LANGUAGE NoImplicitPrelude, LambdaCase, DerivingVia, TemplateHaskellQuotes #-}
{-# LANGUAGE DeriveGeneric, TypeFamilies #-}

-- Helpers for TemplateHaskell instance generators

module AST.Internal.TH
    ( -- Internals for use in TH for sub-classes
      TypeInfo(..), TypeContents(..), CtrTypePattern(..)
    , NodeTypesInfo(..)
    , makeTypeInfo, makeNodeTypesInfo
    , parts, toTuple, matchType
    , applicativeStyle, unapply, getVar, makeConstructorVars
    , consPat, simplifyContext
    ) where

import           AST.Class.Has
import           AST.Class.Pointed
import           AST.Knot (Knot(..), RunKnot, Node, NodeTypesOf)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..), evalStateT, execStateT, gets, modify)
import           Data.Foldable (traverse_)
import           Data.Functor.Const (Const(..))
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
        contents <- evalStateT (childrenTypes var (AppT dst (VarT var))) mempty
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
        KindedTV var (ConT knot) | knot == ''Knot -> pure (res, var)
        PlainTV var -> pure (res, var)
        _ -> fail "expected last argument to be a knot variable"
        where
            res =
                foldl AppT (ConT (D.datatypeName info)) (init xs <&> VarT . D.tvName)

childrenTypes ::
    Name -> Type -> StateT (Set Type) Q TypeContents
childrenTypes var typ =
    do
        did <- gets (^. Lens.contains typ)
        if did
            then pure mempty
            else modify (Lens.contains typ .~ True) *> add (matchType var typ)
    where
        add (NodeFofX ast) = pure mempty { tcChildren = Set.singleton ast }
        add (XofF ast) =
            case unapply ast of
            (ConT name, as) -> childrenTypesFromTypeName name as
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
    | tie == ''Node && k == var =
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

getVar :: Type -> Maybe Name
getVar (VarT x) = Just x
getVar (SigT x _) = getVar x
getVar _ = Nothing

childrenTypesFromTypeName ::
    Name -> [Type] -> StateT (Set Type) Q TypeContents
childrenTypesFromTypeName name args =
    reifyInstances ''KLiftConstraint [typ, VarT constraintVar] & lift
    >>=
    \case
    [] ->
        D.reifyDatatype name
        <&> Just
        & recover (pure Nothing)
        & lift
        >>=
        \case
        Just info ->
            do
                (_, var) <- parts info & lift
                D.datatypeCons info >>= D.constructorFields
                    <&> D.applySubstitution substs
                    & traverse (childrenTypes var)
                    <&> mconcat
            where
                substs =
                    zip (D.datatypeVars info) args
                    <&> Lens._1 %~ D.tvName
                    & Map.fromList
        Nothing ->
            -- Not a datatype, so an embedded type family
            pure mempty { tcEmbeds = Set.singleton typ }
    [TySynInstD ccI (TySynEqn [typI, VarT cI] x)]
        | ccI == ''KLiftConstraint ->
            case unapply typI of
            (ConT n1, argsI) | n1 == name ->
                case traverse getVar argsI of
                Nothing ->
                    error ("TODO: Support Children constraint of flexible instances " <> show typ)
                Just argNames ->
                    childrenTypesFromChildrenConstraint cI (D.applySubstitution substs x)
                    where
                        substs = zip argNames args & Map.fromList
            _ -> error ("ReifyInstances brought wrong typ: " <> show (name, typI))
    xs -> error ("Malformed ChildrenConstraint instance: " <> show xs)
    where
        typ = foldl AppT (ConT name) args

constraintVar :: Name
constraintVar = mkName "constraint"

childrenTypesFromChildrenConstraint ::
    Name -> Type -> StateT (Set Type) Q TypeContents
childrenTypesFromChildrenConstraint c0 c@(AppT (VarT c1) x)
    | c0 == c1 = pure mempty { tcChildren = Set.singleton x }
    | otherwise = error ("TODO: Unsupported ChildrenContraint " <> show c)
childrenTypesFromChildrenConstraint c0 constraints =
    case unapply constraints of
    (ConT cc1, [x, VarT c1])
        | cc1 == ''KLiftConstraint && c0 == c1 ->
            pure mempty { tcEmbeds = Set.singleton x }
    (TupleT{}, xs) ->
        traverse (childrenTypesFromChildrenConstraint c0) xs <&> mconcat
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

getNodeTypes :: Type -> Q Type
getNodeTypes typ =
    reifyInstances ''NodeTypesOf [typ]
    >>=
    \case
    [] -> fail ("Expecting a NodeTypesOf instance for " <> show typ)
    [TySynInstD ccI (TySynEqn [typI] x)]
        | ccI == ''NodeTypesOf ->
            case unapply typI of
            (ConT n1, argsI) | ConT n1 == typeFun ->
                case traverse getVar argsI of
                Nothing ->
                    fail ("TODO: Support NodeTypesOf of flexible instances: " <> show typ)
                Just argNames ->
                    D.applySubstitution substs x & stripSigT & pure
                    where
                        stripSigT (SigT t _) = t
                        stripSigT t = t
                        substs = zip argNames args & Map.fromList
            _ -> fail ("ReifyInstances brought wrong typ: " <> show typ)
    [_] -> fail ("Unsupported NodeTypesOf form for " <> show typ)
    _ -> fail ("Impossible! Several NodeTypesOf instances for " <> show typ)
    where
        (typeFun, args) = unapply typ

consPat :: D.ConstructorInfo -> [(Type, Name)] -> Pat
consPat cons vars =
    ConP (D.constructorName cons) (vars <&> snd <&> VarP)

data NodeTypesInfo = NodeTypesInfo
    { childrenTypesType :: Type
    , childrenTypesPat :: Pat
    , varsForChildTypes :: Map Type Name
    , getEmbedTypes :: Type -> Q Exp
    }

makeNodeTypesInfo :: TypeInfo -> Q NodeTypesInfo
makeNodeTypesInfo typeInfo =
    do
        typ <- getNodeTypes (tiInstance typeInfo)
        let (con, args) = unapply typ
        typeName <-
            case con of
            ConT x -> pure x
            _ -> fail ("unsupported NodeTypesOf: " <> show typ)
        info <- D.reifyDatatype typeName
        let vars = D.datatypeVars info <&> D.tvName
        cons <-
            case D.datatypeCons info of
            [x] -> pure x
            _ -> fail ("NodeTypesOf with more than one constructor: " <> show typ)
        let consVars = makeConstructorVars "c" cons
        let subst = zip vars args & Map.fromList
        let varsForEmbedTypes =
                do
                    (t, name) <- consVars
                    x `AppT` VarT _knot <- [t]
                    ConT cto `AppT` c <- [D.applySubstitution subst x]
                    [(c, name) | cto == ''NodeTypesOf]
                & Map.fromList
        let varsForOtherEmbeds =
                (D.applySubstitution subst typ, wholeVar) :
                do
                    (t, name) <- consVars
                    [] <-
                        do
                            ConT tie `AppT` VarT _ `AppT` _ <- [t]
                            [() | tie == ''Node]
                        & pure
                    x `AppT` VarT _knot <- [t]
                    let xSub = D.applySubstitution subst x
                    [] <-
                        do
                            ConT cto `AppT` _ <- [xSub]
                            [() | cto == ''NodeTypesOf]
                        & pure
                    [(xSub, name)]
                & Map.fromList
        let getEmbed embedType =
                case Map.lookup embedType varsForEmbedTypes of
                Just x -> VarE x & pure
                Nothing ->
                    getNodeTypes embedType
                    <&>
                    \ct ->
                    Map.lookup ct varsForOtherEmbeds
                    & maybe (
                        case ct of
                        ConT constT `AppT` TupleT 0
                            | constT == ''Const ->
                                ConE 'Const `AppE` TupE []
                        _ -> VarE 'hasK `AppE` VarE wholeVar
                        ) VarE
        pure NodeTypesInfo
            { childrenTypesType = typ
            , childrenTypesPat = AsP wholeVar (consPat cons consVars)
            , varsForChildTypes =
                do
                    (t, name) <- consVars
                    ConT tie `AppT` VarT _knot `AppT` c <- [t]
                    [(D.applySubstitution subst c, name) | tie == ''Node]
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
