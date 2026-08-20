{-# LANGUAGE TemplateHaskellQuotes #-}

-- | @Generic@ instance generation for hypertypes.
module Hyper.TH.Generic (makeGeneric) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import qualified Data.Map as Map
import GHC.Generics (Generic)
import qualified GHC.Generics as G
import Hyper.Type (AHyperType (..))
import Language.Haskell.TH
    ( Body (..)
    , Clause (..)
    , Dec (..)
    , DecsQ
    , Exp (..)
    , Name
    , Pat (..)
    , TyLit (..)
    , TySynEqn (..)
    , Type (..)
    , mkName
    , nameBase
    , newName
    )
import qualified Language.Haskell.TH.Datatype as D
import Prelude

-- | Generate a 'Generic' instance for a uniform hypertype GADT.
--
-- Every constructor must return @Type # child@, have no other
-- existential variables or constraints, and may contain any number of fields.
makeGeneric :: Name -> DecsQ
makeGeneric name = do
    info <- D.reifyDatatype name
    let normalArgs = VarT . D.tvName <$> D.datatypeVars info
    case reverse (D.datatypeInstTypes info) of
        SigT (VarT param) (ConT aHyper) : _
            | aHyper == ''AHyperType
            , Just constructors@(_ : _) <- traverse (uniformConstructor param) (D.datatypeCons info) -> do
                h <- newName "h"
                let typ =
                        foldl AppT (ConT name) $
                            init normalArgs <> [PromotedT 'AHyperType `AppT` VarT h]
                pure [makeGenericInstance typ h constructors]
        _ -> fail $ "makeGeneric does not support " <> show name

uniformConstructor :: Name -> D.ConstructorInfo -> Maybe (D.ConstructorInfo, Name)
uniformConstructor param constructor = do
    child <-
        case D.constructorContext constructor of
            [EqualityT `AppT` lhs `AppT` rhs] ->
                match lhs rhs <|> match rhs lhs
            _ -> Nothing
    guard $ all ((== child) . D.tvName) (D.constructorVars constructor)
    pure (constructor, child)
    where
        match (VarT lhs) (PromotedT aHyper `AppT` VarT child)
            | lhs == param && aHyper == 'AHyperType = Just child
        match _ _ = Nothing

makeGenericInstance :: Type -> Name -> [(D.ConstructorInfo, Name)] -> Dec
makeGenericInstance typ h constructors =
    InstanceD
        Nothing
        []
        (ConT ''Generic `AppT` typ)
        [ TySynInstD $ TySynEqn Nothing (ConT ''G.Rep `AppT` typ) representation
        , FunD 'G.from (zipWith fromClause [0 ..] constructors)
        , FunD 'G.to (zipWith toClause [0 ..] constructors)
        ]
    where
        representation = sumType $ constructorRepresentation h <$> constructors
        constructorCount = length constructors
        fromClause index (constructor, _) =
            let variables = fieldNames $ D.constructorFields constructor
            in  Clause
                    [ConP (D.constructorName constructor) [] (VarP <$> variables)]
                    ( NormalB $
                        injectExpression index constructorCount $
                            ConE 'G.M1 `AppE` productExpression variables
                    )
                    []
        toClause index (constructor, _) =
            let variables = fieldNames $ D.constructorFields constructor
            in  Clause
                    [ injectPattern index constructorCount $
                        ConP 'G.M1 [] [productPattern variables]
                    ]
                    (NormalB $ foldl AppE (ConE (D.constructorName constructor)) (VarE <$> variables))
                    []
        fieldNames fields = [mkName $ "field" <> show index | index <- [0 .. length fields - 1]]

constructorRepresentation :: Name -> (D.ConstructorInfo, Name) -> Type
constructorRepresentation h (constructor, child) =
    ConT ''G.M1
        `AppT` ConT ''G.C
        `AppT` constructorMetadata
        `AppT` productType
            ( (\field -> ConT ''G.K1 `AppT` ConT ''G.R `AppT` field)
                . D.applySubstitution (Map.singleton child (VarT h))
                <$> D.constructorFields constructor
            )
    where
        constructorMetadata =
            PromotedT 'G.MetaCons
                `AppT` LitT (StrTyLit $ nameBase $ D.constructorName constructor)
                `AppT` PromotedT 'G.PrefixI
                `AppT` PromotedT 'False

sumType :: [Type] -> Type
sumType = foldr1 (\x xs -> ConT ''(G.:+:) `AppT` x `AppT` xs)

productType :: [Type] -> Type
productType [] = ConT ''G.U1
productType fields = foldr1 (\x xs -> ConT ''(G.:*:) `AppT` x `AppT` xs) fields

productExpression :: [Name] -> Exp
productExpression [] = ConE 'G.U1
productExpression fields = foldr1 productPair (AppE (ConE 'G.K1) . VarE <$> fields)
    where
        productPair x xs = ConE '(G.:*:) `AppE` x `AppE` xs

productPattern :: [Name] -> Pat
productPattern [] = ConP 'G.U1 [] []
productPattern fields = foldr1 productPair (ConP 'G.K1 [] . pure . VarP <$> fields)
    where
        productPair x xs = ConP '(G.:*:) [] [x, xs]

injectExpression :: Int -> Int -> Exp -> Exp
injectExpression _ 1 = id
injectExpression 0 _ = AppE (ConE 'G.L1)
injectExpression index count = AppE (ConE 'G.R1) . injectExpression (index - 1) (count - 1)

injectPattern :: Int -> Int -> Pat -> Pat
injectPattern _ 1 = id
injectPattern 0 _ = \pat -> ConP 'G.L1 [] [pat]
injectPattern index count = \pat -> ConP 'G.R1 [] [injectPattern (index - 1) (count - 1) pat]
