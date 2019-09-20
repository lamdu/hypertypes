{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KHasPlain' instances via @TemplateHaskell@

module AST.TH.HasPlain
    ( makeKHasPlain
    ) where

import           AST.Class.HasPlain
import           AST.Knot (GetKnot)
import           AST.Knot.Pure (Pure, _Pure)
import           AST.TH.Internal.Utils
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Data.Map as Map
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

-- | Generate a 'KHasPlain' instance
makeKHasPlain :: [Name] -> DecsQ
makeKHasPlain = traverse makeOne

makeOne :: Name -> Q Dec
makeOne typeName = makeTypeInfo typeName >>= makeKHasPlainForType

makeKHasPlainForType :: TypeInfo -> Q Dec
makeKHasPlainForType info =
    traverse (makeCtr (tiKnotParam info)) (tiConstructors info)
    <&>
    \ctrs ->
    InstanceD Nothing [] (ConT ''KHasPlain `AppT` tiInstance info)
    [ DataInstD [] ''KPlain [tiInstance info] Nothing (ctrs <&> (^. Lens._1))
        [DerivClause (Just StockStrategy) [ConT ''Eq, ConT ''Ord, ConT ''Show]]
    , FunD 'kPlain
        [ Clause []
            ( NormalB
                (InfixE
                    (Just (VarE 'Lens.iso `AppE` VarE fromPlain `AppE` VarE toPlain))
                    (VarE '(.))
                    (Just (VarE 'Lens.from `AppE` VarE '_Pure))
                )
            )
            [ FunD toPlain (ctrs <&> (^. Lens._2))
            , FunD fromPlain (ctrs <&> (^. Lens._3))
            ]
        ]
    ]
    where
        toPlain = mkName "toPlain"
        fromPlain = mkName "fromPlain"

data FieldInfo = FieldInfo
    { fieldPlainType :: Type
    , fieldToPlain :: Exp -> Exp
    , fieldFromPlain :: Exp -> Exp
    }

data EmbedInfo = EmbedInfo
    { embedCtr :: Name
    , embedFields :: [Field]
    }

data Field
    = NodeField FieldInfo
    | EmbedFields EmbedInfo

makeCtr :: Name -> (Name, [Either Type CtrTypePattern]) -> Q (Con, Clause, Clause)
makeCtr knot (cName, cFields) =
    traverse forField cFields
    <&>
    \xs ->
    let plainTypes = xs >>= plainFieldTypes
        cVars = [0::Int ..] <&> show <&> ('x':) <&> mkName & take (length plainTypes)
    in
    ( plainTypes
        <&> (Bang NoSourceUnpackedness NoSourceStrictness, )
        & NormalC pcon
    , zipWith ($) (xs >>= toPlainFields) (cVars <&> VarE)
        & foldl AppE (ConE pcon)
        & NormalB
        & \x ->
            Clause [ConP cName (toPlainPat cVars xs ^. Lens._1)] x []
    , fromPlainFields cVars xs ^. Lens._1
        & foldl AppE (ConE cName)
        & NormalB
        & \x -> Clause [ConP pcon (cVars <&> VarP)] x []
    )
    where
        plainFieldTypes (NodeField x) = [fieldPlainType x]
        plainFieldTypes (EmbedFields x) = embedFields x >>= plainFieldTypes
        toPlainFields (NodeField x) = [fieldToPlain x]
        toPlainFields (EmbedFields x) = embedFields x >>= toPlainFields
        toPlainPat cs [] = ([], cs)
        toPlainPat (c:cs) (NodeField{} : xs) = toPlainPat cs xs & Lens._1 %~ (VarP c :)
        toPlainPat cs0 (EmbedFields x : xs) =
            toPlainPat cs1 xs & Lens._1 %~ (ConP (embedCtr x) r :)
            where
                (r, cs1) = toPlainPat cs0 (embedFields x)
        toPlainPat [] _ = error "out of variables"
        fromPlainFields cs [] = ([], cs)
        fromPlainFields (c:cs) (NodeField x : xs) =
            fromPlainFields cs xs & Lens._1 %~ (fieldFromPlain x (VarE c) :)
        fromPlainFields cs0 (EmbedFields x : xs) =
            fromPlainFields cs1 xs & Lens._1 %~ (foldl AppE (ConE (embedCtr x)) r :)
            where
                (r, cs1) = fromPlainFields cs0 (embedFields x)
        fromPlainFields [] _ = error "out of variables"
        pcon =
            show cName & reverse & takeWhile (/= '.') & reverse
            & (<> "P") & mkName
        forField (Left t) =
            NodeField FieldInfo
            { fieldPlainType = normalizeType t
            , fieldToPlain = id
            , fieldFromPlain = id
            } & pure
        forField (Right x) = forPat x
        forPat (Node x) = forGen x
        forPat (GenEmbed x) = forGen x
        forPat (InContainer t p) =
            NodeField FieldInfo
            { fieldPlainType = t `AppT` patType p
            , fieldToPlain = AppE (VarE 'fmap `AppE` InfixE (Just (VarE 'kPlain)) (VarE '(#)) Nothing)
            , fieldFromPlain = AppE (VarE 'fmap `AppE` InfixE Nothing (VarE '(^.)) (Just (VarE 'kPlain)))
            } & pure
            where
                patType (Node x) = ConT ''KPlain `AppT` x
                patType (GenEmbed x) = ConT ''KPlain `AppT` x
                patType (FlatEmbed x) = ConT ''KPlain `AppT` tiInstance x
                patType (InContainer t' p') = t' `AppT` patType p'
        forPat (FlatEmbed x) =
            case tiConstructors x of
            [(n, xs)] -> traverse forField xs <&> EmbedInfo n <&> EmbedFields
            _ -> forGen (tiInstance x)
        forGen t =
            case unapply t of
            (ConT c, args) ->
                do
                    inner <- D.reifyDatatype c
                    let subst =
                            args <> [VarT knot]
                            & zip (D.datatypeVars inner <&> D.tvName)
                            & Map.fromList
                    case D.datatypeCons inner of
                        [x] ->
                            D.constructorFields x
                            <&> D.applySubstitution subst
                            & traverse (matchType knot)
                            >>= traverse forField
                            <&> EmbedInfo (D.constructorName x)
                            <&> EmbedFields
                        _ -> gen
            _ -> gen
            where
                gen =
                    NodeField FieldInfo
                    { fieldPlainType = ConT ''KPlain `AppT` t
                    , fieldToPlain = InfixE (Just (VarE 'kPlain)) (VarE '(#)) . Just
                    , fieldFromPlain = \f -> InfixE (Just f) (VarE '(^.)) (Just (VarE 'kPlain))
                    } & pure
        normalizeType (ConT g `AppT` VarT v)
            | g == ''GetKnot && v == knot = ConT ''Pure
        normalizeType (x `AppT` y) = normalizeType x `AppT` normalizeType y
        normalizeType x = x
