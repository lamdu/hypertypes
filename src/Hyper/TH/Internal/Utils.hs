{-# LANGUAGE TemplateHaskellQuotes, DerivingVia #-}

-- Helpers for TemplateHaskell instance generators

module Hyper.TH.Internal.Utils
    ( -- Internals for use in TH for sub-classes
      TypeInfo(..), TypeContents(..), CtrTypePattern(..), NodeWitnesses(..)
    , makeTypeInfo, makeNodeOf
    , parts, toTuple, matchType
    , applicativeStyle, unapply, getVar, makeConstructorVars
    , consPat, simplifyContext, childrenTypes
    ) where

import           Hyper.Class.Nodes
import           Hyper.Type (AHyperType(..), GetHyperType, type (#))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (State, evalState, execStateT, gets, modify)
import           Data.Foldable (traverse_)
import           Data.List (nub)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Generic.Data (Generically(..))
import           GHC.Generics (Generic)
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

data TypeInfo = TypeInfo
    { tiName :: Name
    , tiInstance :: Type
    , tiHyperParam :: Name
    , tiConstructors :: [(Name, [Either Type CtrTypePattern])]
    } deriving Show

data TypeContents = TypeContents
    { tcChildren :: Set Type
    , tcEmbeds :: Set Type
    , tcOthers :: Set Type
    } deriving (Show, Generic)
    deriving (Semigroup, Monoid) via Generically TypeContents

data CtrTypePattern
    = Node Type
    | FlatEmbed TypeInfo
    | GenEmbed Type
    | InContainer Type CtrTypePattern
    deriving Show

makeTypeInfo :: Name -> Q TypeInfo
makeTypeInfo name =
    do
        info <- D.reifyDatatype name
        (dst, var) <- parts info
        let makeCons c =
                traverse (matchType var) (D.constructorFields c)
                <&> (D.constructorName c, )
        cons <- traverse makeCons (D.datatypeCons info)
        pure TypeInfo
            { tiName = name
            , tiInstance = dst
            , tiHyperParam = var
            , tiConstructors = cons
            }

parts :: D.DatatypeInfo -> Q (Type, Name)
parts info =
    case D.datatypeVars info of
    [] -> fail "expected type constructor which requires arguments"
    xs ->
        case last xs of
        KindedTV var (ConT aHyper) | aHyper == ''AHyperType -> pure (res, var)
        PlainTV var -> pure (res, var)
        _ -> fail "expected last argument to be a AHyperType variable"
        where
            res =
                foldl AppT (ConT (D.datatypeName info)) (init xs <&> VarT . D.tvName)

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
                modify (Lens.contains (tiInstance info) .~ True) *>
                traverse addPat (tiConstructors info ^.. traverse . Lens._2 . traverse . Lens._Right)
                    <&> mconcat
    where
        addPat (FlatEmbed inner) = childrenTypesH inner
        addPat (Node x) = pure mempty { tcChildren = Set.singleton x }
        addPat (GenEmbed x) = pure mempty { tcEmbeds = Set.singleton x }
        addPat (InContainer _ x) = addPat x

unapply :: Type -> (Type, [Type])
unapply =
    go []
    where
        go as (SigT x _) = go as x
        go as (AppT f a) = go (a:as) f
        go as x = (x, as)

matchType :: Name -> Type -> Q (Either Type CtrTypePattern)
matchType var (ConT get `AppT` VarT k `AppT` (PromotedT aHyper `AppT` x))
    | get == ''GetHyperType && aHyper == 'AHyperType && k == var =
        Node x & Right & pure
matchType var (InfixT (VarT k) hash x)
    | hash == ''(#) && k == var =
        Node x & Right & pure
matchType var (ConT hash `AppT` VarT k `AppT` x)
    | hash == ''(#) && k == var =
        Node x & Right & pure
matchType var (x `AppT` VarT k)
    | k == var && x /= ConT ''GetHyperType =
        case unapply x of
        (ConT c, args) ->
            do
                inner <- D.reifyDatatype c
                let innerVars = D.datatypeVars inner <&> D.tvName
                let subst =
                        args <> [VarT var]
                        & zip innerVars
                        & Map.fromList
                let makeCons i =
                        D.constructorFields i
                        <&> D.applySubstitution subst
                        & traverse (matchType var)
                        <&> (D.constructorName i, )
                traverse makeCons (D.datatypeCons inner)
            <&>
            \cons ->
            if var `notElem` (D.freeVariablesWellScoped (cons ^.. traverse . Lens._2 . traverse . Lens._Left) <&> D.tvName)
            then
                FlatEmbed TypeInfo
                { tiName = c
                , tiInstance = x
                , tiHyperParam = var
                , tiConstructors = cons
                }
            else
                GenEmbed x
        _ -> GenEmbed x & pure
        <&> Right
matchType var x@(AppT f a) =
    -- TODO: check if applied over a functor-kinded type.
    matchType var a
    <&>
    \case
    Left{} -> Left x
    Right pat -> InContainer f pat & Right
matchType _ t = Left t & pure

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

makeConstructorVars :: String -> [a] -> [(a, Name)]
makeConstructorVars prefix fields =
    [0::Int ..] <&> show <&> (('_':prefix) <>) <&> mkName
    & zip fields

consPat :: Name -> [(a, Name)] -> Pat
consPat c vars =
    ConP c (vars <&> snd <&> VarP)

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

data NodeWitnesses = NodeWitnesses
    { nodeWit :: Type -> Exp
    , embedWit :: Type -> Exp
    , nodeWitCtrs :: [Name]
    , embedWitCtrs :: [Name]
    }

makeNodeOf :: TypeInfo -> ([Con], NodeWitnesses)
makeNodeOf info =
    ( (nodes <&> Lens._1 %~ nodeGadtType) <> (embeds <&> Lens._1 %~ embedGadtType)
        <&> \(t, n) -> GadtC [n] [] t
    , NodeWitnesses
        { nodeWit = nodes <&> Lens._2 %~ ConE & Map.fromList & getWit
        , embedWit = embeds <&> Lens._2 %~ ConE & Map.fromList & getWit
        , nodeWitCtrs = nodes <&> snd
        , embedWitCtrs = embeds <&> snd
        }
    )
    where
        niceTypeName = tiName info & show & makeNiceName
        makeNiceName = reverse . takeWhile (/= '.') . reverse
        nodeBase = "W_" <> niceTypeName <> "_"
        embedBase = "E_" <> niceTypeName <> "_"
        pats = tiConstructors info >>= snd
        makeNiceType (ConT x) = makeNiceName (show x)
        makeNiceType (AppT x y) = makeNiceType x <> "_" <> makeNiceType y
        makeNiceType (VarT x) = takeWhile (/= '_') (show x)
        makeNiceType (SigT x _) = makeNiceType x
        makeNiceType x = error ("TODO: Witness name generator is partial! Need to support " <> show x)
        nodes =
            pats ^.. traverse . Lens._Right >>= nodesForPat & nub
            <&> \t -> (t, mkName (nodeBase <> makeNiceType t))
        nodesForPat (Node t) = [t]
        nodesForPat (InContainer _ pat) = nodesForPat pat
        nodesForPat (FlatEmbed x) = tiConstructors x ^.. traverse . Lens._2 . traverse . Lens._Right >>= nodesForPat
        nodesForPat _ = []
        nodeGadtType t = ConT ''HWitness `AppT` tiInstance info `AppT` t
        embeds =
            pats ^.. traverse . Lens._Right >>= embedsForPat & nub
            <&> \t -> (t, mkName (embedBase <> makeNiceType t))
        embedsForPat (GenEmbed t) = [t]
        embedsForPat (InContainer _ pat) = embedsForPat pat
        embedsForPat (FlatEmbed x) = tiConstructors x ^.. traverse . Lens._2 . traverse . Lens._Right >>= embedsForPat
        embedsForPat _ = []
        embedGadtType t =
            ArrowT
            `AppT` (ConT ''HWitness `AppT` t `AppT` VarT nodeVar)
            `AppT` (ConT ''HWitness `AppT` tiInstance info `AppT` VarT nodeVar)
        nodeVar = mkName "node"
        getWit :: Map Type Exp -> Type -> Exp
        getWit m k =
            m ^? Lens.ix k
            & fromMaybe (LitE (StringL ("Cant find witness for " <> show k <> " in " <> show m)))
