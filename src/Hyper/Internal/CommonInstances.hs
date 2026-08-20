{-# LANGUAGE TemplateHaskellQuotes #-}

module Hyper.Internal.CommonInstances (makeCommonInstances) where

import Control.Applicative ((<|>))
import Control.DeepSeq (NFData)
import Control.Monad (guard)
import Data.Binary (Binary)
import Generics.Constraints (Constraints)
import Hyper.TH.Generic (makeGeneric)
import Hyper.Type (AHyperType (..))
import Language.Haskell.TH
    ( DecsQ
    , Name
    , Q
    , Type (..)
    , conT
    , instanceD
    , newName
    , standaloneDerivD
    )
import qualified Language.Haskell.TH.Datatype as D
import Prelude

-- Derive a specific list of classes that types in hypertypes implement.
makeCommonInstances :: [Name] -> DecsQ
makeCommonInstances = fmap concat . traverse makeForType
    where
        makeForType name = do
            (typ, needsGeneric) <- commonInstanceInfo name
            genericInstance <- if needsGeneric then makeGeneric name else pure []
            commonInstances <-
                traverse (makeDeriving typ) [''Eq, ''Ord, ''Show]
                    <> traverse (makeInstance typ) [''Binary, ''NFData]
            pure $ genericInstance <> commonInstances
        makeDeriving typ cls =
            standaloneDerivD
                (pure <$> [t|Constraints $(pure typ) $(conT cls)|])
                [t|$(conT cls) $(pure typ)|]
        makeInstance typ cls =
            instanceD
                (pure <$> [t|Constraints $(pure typ) $(conT cls)|])
                [t|$(conT cls) $(pure typ)|]
                []

commonInstanceInfo :: Name -> Q (Type, Bool)
commonInstanceInfo name = do
    info <- D.reifyDatatype name
    let normalArgs = VarT . D.tvName <$> D.datatypeVars info
    case reverse (D.datatypeInstTypes info) of
        SigT (VarT param) (ConT aHyper) : _
            | aHyper == ''AHyperType
            , Just (_ : _) <- traverse (uniformConstructor param) (D.datatypeCons info) -> do
                h <- newName "h"
                let typ =
                        foldl AppT (ConT name) $
                            init normalArgs <> [PromotedT 'AHyperType `AppT` VarT h]
                pure (typ, True)
        _ -> pure (foldl AppT (ConT name) normalArgs, False)

uniformConstructor :: Name -> D.ConstructorInfo -> Maybe Name
uniformConstructor param constructor = do
    child <-
        case D.constructorContext constructor of
            [EqualityT `AppT` lhs `AppT` rhs] ->
                match lhs rhs <|> match rhs lhs
            _ -> Nothing
    guard $ all ((== child) . D.tvName) (D.constructorVars constructor)
    pure child
    where
        match (VarT lhs) (PromotedT aHyper `AppT` VarT child)
            | lhs == param && aHyper == 'AHyperType = Just child
        match _ _ = Nothing
