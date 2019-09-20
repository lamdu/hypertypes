{-# LANGUAGE TemplateHaskellQuotes, DerivingVia #-}

-- Helpers for TemplateHaskell instance generators

module AST.TH.Internal.Utils
    ( -- Internals for use in TH for sub-classes
      TypeInfo(..), TypeContents(..), CtrTypePattern(..), NodeWitnesses(..)
    , makeTypeInfo, makeNodeOf
    , parts, toTuple, matchType
    , applicativeStyle, unapply, getVar, makeConstructorVars
    , consPat, simplifyContext
    ) where

import           AST.Class.Nodes
import           AST.Knot (Knot(..), GetKnot, type (#))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..), evalStateT, execStateT, gets, modify)
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
    , tiKnotParam :: Name
    , tiContents :: TypeContents
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
    | Embed Type
    | InContainer Type CtrTypePattern
    deriving Show

makeTypeInfo :: Name -> Q TypeInfo
makeTypeInfo name =
    do
        info <- D.reifyDatatype name
        (dst, var) <- parts info
        contents <- evalStateT (childrenTypes var (AppT dst (VarT var))) mempty
        pure TypeInfo
            { tiName = name
            , tiInstance = dst
            , tiKnotParam = var
            , tiContents = contents
            , tiConstructors =
                D.datatypeCons info
                <&> \x -> (D.constructorName x, D.constructorFields x <&> matchType var)
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
        add (Right x) = addPat x
        add Left{} = pure mempty
        addPat (Node ast) = pure mempty { tcChildren = Set.singleton ast }
        addPat (Embed ast) =
            case unapply ast of
            (ConT name, as) -> childrenTypesFromTypeName name as
            (x@VarT{}, as) -> pure mempty { tcEmbeds = Set.singleton (foldl AppT x as) }
            _ -> pure mempty
        addPat (InContainer _ pat) = addPat pat

unapply :: Type -> (Type, [Type])
unapply =
    go []
    where
        go as (SigT x _) = go as x
        go as (AppT f a) = go (a:as) f
        go as x = (x, as)

matchType :: Name -> Type -> Either Type CtrTypePattern
matchType var (ConT getKnot `AppT` VarT k `AppT` (PromotedT knot `AppT` x))
    | getKnot == ''GetKnot && knot == 'Knot && k == var =
        Node x & Right
matchType var (InfixT (VarT k) hash x)
    | hash == ''(#) && k == var =
        Node x & Right
matchType var (ConT hash `AppT` VarT k `AppT` x)
    | hash == ''(#) && k == var =
        Node x & Right
matchType var (x `AppT` VarT k)
    | k == var && x /= ConT ''GetKnot =
        Embed x & Right
matchType var x@(AppT f a) =
    -- TODO: check if applied over a functor-kinded type.
    case matchType var a of
    Left{} -> Left x
    Right pat -> InContainer f pat & Right
matchType _ t = Left t

getVar :: Type -> Maybe Name
getVar (VarT x) = Just x
getVar (SigT x _) = getVar x
getVar _ = Nothing

childrenTypesFromTypeName ::
    Name -> [Type] -> StateT (Set Type) Q TypeContents
childrenTypesFromTypeName name args =
    reifyInstances ''KNodesConstraint [typ, VarT constraintVar] & lift
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
        | ccI == ''KNodesConstraint ->
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
        | cc1 == ''KNodesConstraint && c0 == c1 ->
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
        nodesForPat _ = []
        nodeGadtType t = ConT ''KWitness `AppT` tiInstance info `AppT` t
        embeds =
            pats ^.. traverse . Lens._Right >>= embedsForPat & nub
            <&> \t -> (t, mkName (embedBase <> makeNiceType t))
        embedsForPat (Embed t) = [t]
        embedsForPat (InContainer _ pat) = embedsForPat pat
        embedsForPat _ = []
        embedGadtType t =
            ArrowT
            `AppT` (ConT ''KWitness `AppT` t `AppT` VarT nodeVar)
            `AppT` (ConT ''KWitness `AppT` tiInstance info `AppT` VarT nodeVar)
        nodeVar = mkName "node"
        getWit :: Map Type Exp -> Type -> Exp
        getWit m k =
            m ^? Lens.ix k
            & fromMaybe (LitE (StringL ("Cant find witness for " <> show k <> " in " <> show m)))
