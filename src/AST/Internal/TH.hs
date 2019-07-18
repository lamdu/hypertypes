{-# LANGUAGE NoImplicitPrelude, LambdaCase, DerivingVia, TemplateHaskellQuotes #-}
{-# LANGUAGE DeriveGeneric #-}

-- Helpers for TemplateHaskell instance generators

module AST.Internal.TH
    ( -- Internals for use in TH for sub-classes
      TypeInfo(..), TypeContents(..), CtrTypePattern(..)
    , makeTypeInfo, parts, toTuple, matchType, isPolymorphic
    , applicativeStyle, unapply, getVar
    ) where

import           AST.Class.Pointed
import           AST.Knot (Knot(..), RunKnot, Tie)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..), evalStateT, gets, modify)
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

applicativeStyle :: Exp -> [Exp] -> Exp
applicativeStyle f =
    foldl ap (AppE (VarE 'pure) f)
    where
        ap x y = InfixE (Just x) (VarE '(<*>)) (Just y)
