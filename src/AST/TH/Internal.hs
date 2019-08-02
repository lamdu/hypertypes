{-# LANGUAGE LambdaCase, TemplateHaskellQuotes #-}

-- Helpers for TemplateHaskell instance generators

module AST.TH.Internal
    ( -- Internals for use in TH for sub-classes
      TypeInfo(..), CtrTypePattern(..)
    , NodeTypesInfo(..)
    , makeTypeInfo, makeNodeTypesInfo
    , parts, toTuple, matchType
    , applicativeStyle, unapply, getVar, makeConstructorVars
    , consPat, simplifyContext
    ) where

import           AST.Class
import           AST.Class.Has
import           AST.Knot (Knot(..), RunKnot, Node)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (execStateT)
import           Data.Foldable (traverse_)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

data TypeInfo = TypeInfo
    { tiInstance :: Type
    , tiVar :: Name
    , tiCons :: [D.ConstructorInfo]
    } deriving Show

makeTypeInfo :: Name -> Q TypeInfo
makeTypeInfo name =
    do
        info <- D.reifyDatatype name
        (dst, var) <- parts info
        pure TypeInfo
            { tiInstance = dst
            , tiVar = var
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
        cons <-
            case D.datatypeCons info of
            [x] -> pure x
            _ -> fail ("NodeTypesOf with more than one constructor: " <> show typ)
        let consVars = makeConstructorVars "c" cons
        let kindVars =
                D.datatypeVars info <&> D.tvKind >>= D.freeVariables
                & Set.fromList
        let vars =
                D.datatypeVars info <&> D.tvName
                & filter (not . (`Set.member` kindVars))
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
                    & maybe (VarE 'hasK `AppE` VarE wholeVar) VarE
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
