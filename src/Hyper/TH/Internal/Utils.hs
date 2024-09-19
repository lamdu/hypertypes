{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TemplateHaskell #-}

-- Helpers for TemplateHaskell instance generators

module Hyper.TH.Internal.Utils
    ( -- Internals for use in TH for sub-classes
      TypeInfo (..)
    , TypeContents (..)
    , CtrTypePattern (..)
    , NodeWitnesses (..)
    , makeTypeInfo
    , makeNodeOf
    , parts
    , toTuple
    , matchType
    , niceName
    , mkNiceTypeName
    , applicativeStyle
    , unapply
    , getVar
    , makeConstructorVars
    , consPat
    , simplifyContext
    , childrenTypes
    ) where

import qualified Control.Lens as Lens
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Trans.State (State, evalState, execStateT, gets, modify)
import qualified Data.Char as Char
import Data.List (intercalate, nub)
import qualified Data.Map as Map
import Generic.Data (Generically (..))
import Hyper.Class.Nodes (HWitness (..))
import Hyper.Type (AHyperType (..), GetHyperType, type (:#))
import Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D
import Language.Haskell.TH.Datatype.TyVarBndr

import Hyper.Internal.Prelude

data TypeInfo = TypeInfo
    { tiName :: Name
    , tiInstance :: Type
    , tiParams :: [TyVarBndrUnit]
    , tiHyperParam :: Name
    , tiConstructors :: [(Name, D.ConstructorVariant, [Either Type CtrTypePattern])]
    }
    deriving (Show)

data TypeContents = TypeContents
    { tcChildren :: Set Type
    , tcEmbeds :: Set Type
    , tcOthers :: Set Type
    }
    deriving (Show, Generic)
    deriving (Semigroup, Monoid) via Generically TypeContents

data CtrTypePattern
    = Node Type
    | FlatEmbed TypeInfo
    | GenEmbed Type
    | InContainer Type CtrTypePattern
    deriving (Show)

makeTypeInfo :: Name -> Q TypeInfo
makeTypeInfo name =
    do
        info <- D.reifyDatatype name
        (dst, var) <- parts info
        let makeCons c =
                traverse (matchType name var) (D.constructorFields c)
                    <&> (D.constructorName c,D.constructorVariant c,)
        cons <- traverse makeCons (D.datatypeCons info)
        let unkindToVar = \case
                VarT v -> pure $ PlainTV v ()
                SigT (VarT v) _k -> pure $ PlainTV v ()
                _ -> fail "expected only variabled to be applied to data type"
        params <- traverse unkindToVar . init . D.datatypeInstTypes $ info
        pure
            TypeInfo
                { tiName = name
                , tiInstance = dst
                , tiParams = params
                , tiHyperParam = var
                , tiConstructors = cons
                }

parts :: D.DatatypeInfo -> Q (Type, Name)
parts info =
    case D.datatypeInstTypes info of
        [] -> fail "expected type constructor which requires arguments"
        xs ->
            case last xs of
                SigT (VarT var) (ConT aHyper)
                    | aHyper == ''AHyperType -> pure (res, var)
                _ -> fail "expected last argument to be a AHyperType variable"
            where
                unkind = \case
                    SigT a _k -> a
                    a -> a
                res =
                    foldl AppT (ConT (D.datatypeName info)) (init xs <&> unkind)

childrenTypes :: TypeInfo -> TypeContents
childrenTypes info = evalState (childrenTypesH info) mempty

childrenTypesH ::
    TypeInfo -> State (Set Type) TypeContents
childrenTypesH info =
    do
        did <- gets (^. Lens.contains (tiInstance info))
        if did
            then pure mempty
            else
                modify (Lens.contains (tiInstance info) .~ True)
                    *> traverse addPat (tiConstructors info ^.. traverse . Lens._3 . traverse . Lens._Right)
                    <&> mconcat
    where
        addPat (FlatEmbed inner) = childrenTypesH inner
        addPat (Node x) = pure mempty{tcChildren = mempty & Lens.contains x .~ True}
        addPat (GenEmbed x) = pure mempty{tcEmbeds = mempty & Lens.contains x .~ True}
        addPat (InContainer _ x) = addPat x

unapply :: Type -> (Type, [Type])
unapply =
    go []
    where
        go as (SigT x _) = go as x
        go as (AppT f a) = go (a : as) f
        go as x = (x, as)

matchType :: Name -> Name -> Type -> Q (Either Type CtrTypePattern)
matchType _ var (ConT get `AppT` VarT h `AppT` (PromotedT aHyper `AppT` x))
    | get == ''GetHyperType && aHyper == 'AHyperType && h == var =
        Node x & Right & pure
matchType _ var (InfixT (VarT h) hash x)
    | hash == ''(:#) && h == var =
        Node x & Right & pure
matchType _ var (ConT hash `AppT` VarT h `AppT` x)
    | hash == ''(:#) && h == var =
        Node x & Right & pure
matchType top var (x `AppT` VarT h)
    | h == var && x /= ConT ''GetHyperType =
        case unapply x of
            (ConT c, args) | c /= top ->
                do
                    inner <- D.reifyDatatype c
                    let innerVars = D.datatypeVars inner <&> D.tvName
                    let subst =
                            args <> [VarT var]
                                & zip innerVars
                                & Map.fromList
                    let makeCons i =
                            traverse (matchType top var . D.applySubstitution subst) (D.constructorFields i)
                                <&> (D.constructorName i,D.constructorVariant i,)
                    cons <- traverse makeCons (D.datatypeCons inner)
                    if var `notElem` (D.freeVariablesWellScoped (cons ^.. traverse . Lens._3 . traverse . Lens._Left) <&> D.tvName)
                        then
                            FlatEmbed
                                TypeInfo
                                    { tiName = c
                                    , tiInstance = x
                                    , tiParams = D.datatypeVars inner & init
                                    , tiHyperParam = var
                                    , tiConstructors = cons
                                    }
                                & pure
                        else GenEmbed x & pure
            _ -> GenEmbed x & pure
            <&> Right
matchType top var x@(AppT f a) =
    -- TODO: check if applied over a functor-kinded type.
    matchType top var a
        <&> \case
            Left{} -> Left x
            Right pat -> InContainer f pat & Right
matchType _ _ t = Left t & pure

getVar :: Type -> Maybe Name
getVar (VarT x) = Just x
getVar (SigT x _) = getVar x
getVar _ = Nothing

toTuple :: Foldable t => t Type -> Type
toTuple xs = foldl AppT (TupleT (length xs)) xs

applicativeStyle :: Q Exp -> [Q Exp] -> Q Exp
applicativeStyle f =
    foldl ap [|pure $f|]
    where
        ap x y = [|$x <*> $y|]

makeConstructorVars :: String -> [a] -> [(a, Name)]
makeConstructorVars prefix fields =
    [0 :: Int ..]
        <&> mkName . (('_' : prefix) <>) . show
        & zip fields

consPat :: Name -> [(a, Name)] -> Q Pat
consPat c = conP c . (<&> varP . snd)

simplifyContext :: [Pred] -> CxtQ
simplifyContext preds =
    execStateT (goPreds preds) (mempty :: Set (Name, [Type]), mempty :: Set Pred)
        <&> (^.. Lens._2 . Lens.folded)
    where
        goPreds = traverse_ (go . unapply)
        go (c, [VarT v]) =
            -- Work-around reifyInstances returning instances for type variables
            -- by not checking.
            yep c [VarT v]
        go (ConT c, xs) =
            Lens.use (Lens._1 . Lens.contains key)
                >>= \case
                    True -> pure () -- already checked
                    False ->
                        do
                            Lens._1 . Lens.contains key .= True
                            reifyInstances c xs
                                & lift
                                >>= \case
                                    [InstanceD _ context other _] ->
                                        D.unifyTypes [other, foldl AppT (ConT c) xs]
                                            & lift
                                            <&> (`D.applySubstitution` context)
                                            >>= goPreds
                                    _ -> yep (ConT c) xs
            where
                key = (c, xs)
        go (c, xs) = yep c xs
        yep c xs = Lens._2 . Lens.contains (foldl AppT c xs) .= True

data NodeWitnesses = NodeWitnesses
    { nodeWit :: Type -> Q Exp
    , embedWit :: Type -> Q Exp
    , nodeWitCtrs :: [Name]
    , embedWitCtrs :: [Name]
    }

niceName :: Name -> String
niceName = reverse . takeWhile (/= '.') . reverse . show

makeNodeOf :: TypeInfo -> ([Type -> Q Con], NodeWitnesses)
makeNodeOf info =
    ( (nodes <&> nodeGadtType) <> (embeds <&> embedGadtType)
    , NodeWitnesses
        { nodeWit = nodes & Map.fromList & getWit <&> \x -> [|HWitness $(conE x)|]
        , embedWit = embeds & Map.fromList & getWit <&> \x -> [|HWitness . $(conE x)|]
        , nodeWitCtrs = nodes <&> snd
        , embedWitCtrs = embeds <&> snd
        }
    )
    where
        niceTypeName = tiName info & niceName
        nodeBase = "W_" <> niceTypeName <> "_"
        embedBase = "E_" <> niceTypeName <> "_"
        pats = tiConstructors info >>= (^. Lens._3)
        nodes =
            pats ^.. traverse . Lens._Right
                >>= nodesForPat
                & nub
                <&> \t -> (t, mkName (nodeBase <> mkNiceTypeName t))
        nodesForPat (Node t) = [t]
        nodesForPat (InContainer _ pat) = nodesForPat pat
        nodesForPat (FlatEmbed x) = tiConstructors x ^.. traverse . Lens._3 . traverse . Lens._Right >>= nodesForPat
        nodesForPat _ = []
        nodeGadtType (t, n) c = gadtC [n] [] (pure (c `AppT` t))
        embeds =
            pats ^.. traverse . Lens._Right
                >>= embedsForPat
                & nub
                <&> \t -> (t, mkName (embedBase <> mkNiceTypeName t))
        embedsForPat (GenEmbed t) = [t]
        embedsForPat (InContainer _ pat) = embedsForPat pat
        embedsForPat (FlatEmbed x) = tiConstructors x ^.. traverse . Lens._3 . traverse . Lens._Right >>= embedsForPat
        embedsForPat _ = []
        embedGadtType (t, n) c =
            gadtC
                [n]
                [ bangType
                    (bang noSourceUnpackedness noSourceStrictness)
                    [t|HWitness $(pure t) $nodeVar|]
                ]
                [t|$(pure c) $nodeVar|]
        nodeVar = mkName "node" & varT
        getWit :: Map Type Name -> Type -> Name
        getWit m h =
            m ^? Lens.ix h
                & fromMaybe (error ("Cant find witness for " <> show h <> " in " <> show m))

mkNiceTypeName :: Type -> String
mkNiceTypeName =
    intercalate "_" . makeNiceType
    where
        makeNiceType (ConT x) =
            case niceName x of
                n@(c : _) | Char.isAlpha c -> [n]
                _ -> [] -- Skip operators
        makeNiceType (AppT x y) = makeNiceType x <> makeNiceType y
        makeNiceType (VarT x) = [takeWhile (/= '_') (show x)]
        makeNiceType (SigT x _) = makeNiceType x
        makeNiceType x = error ("TODO: Witness name generator is partial! Need to support " <> show x)
