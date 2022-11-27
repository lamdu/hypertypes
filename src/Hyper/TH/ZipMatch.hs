{-# LANGUAGE TemplateHaskell #-}

-- | Generate 'ZipMatch' instances via @TemplateHaskell@
module Hyper.TH.ZipMatch
    ( makeZipMatch
    ) where

import Control.Lens (both)
import Hyper.Class.ZipMatch (ZipMatch (..))
import Hyper.TH.Internal.Utils
import Language.Haskell.TH
import Language.Haskell.TH.Datatype (ConstructorVariant)

import Hyper.Internal.Prelude

-- | Generate a 'ZipMatch' instance
makeZipMatch :: Name -> DecsQ
makeZipMatch typeName =
    do
        info <- makeTypeInfo typeName
        -- (dst, var) <- parts info
        let ctrs = tiConstructors info <&> makeZipMatchCtr
        instanceD
            (ctrs >>= ccContext & sequenceA >>= simplifyContext)
            (appT (conT ''ZipMatch) (pure (tiInstance info)))
            [ InlineP 'zipMatch Inline FunLike AllPhases & PragmaD & pure
            , funD 'zipMatch ((ctrs <&> ccClause) <> [tailClause])
            ]
            <&> (: [])
    where
        tailClause = clause [wildP, wildP] (normalB [|Nothing|]) []

data CtrCase = CtrCase
    { ccClause :: Q Clause
    , ccContext :: [Q Pred]
    }

makeZipMatchCtr :: (Name, ConstructorVariant, [Either Type CtrTypePattern]) -> CtrCase
makeZipMatchCtr (cName, _, cFields) =
    CtrCase
        { ccClause = clause [con fst, con snd] body []
        , ccContext = fieldParts >>= zmfContext
        }
    where
        con f = conP cName (cVars <&> f <&> varP)
        cVars =
            [0 :: Int ..]
                <&> show
                <&> (\n -> (mkName ('x' : n), mkName ('y' : n)))
                & take (length cFields)
        body
            | null checks = normalB bodyExp
            | otherwise = guardedB [(,) <$> normalG (foldl1 mkAnd checks) <*> bodyExp]
        checks = fieldParts >>= zmfConds
        mkAnd x y = [|$x && $y|]
        fieldParts = zipWith field (cVars <&> both %~ varE) cFields
        bodyExp = applicativeStyle (conE cName) (fieldParts <&> zmfResult)
        field (x, y) (Right Node{}) =
            ZipMatchField
                { zmfResult = [|Just ($x :*: $y)|]
                , zmfConds = []
                , zmfContext = []
                }
        field (x, y) (Right (GenEmbed t)) = embed t x y
        field (x, y) (Right (FlatEmbed t)) = embed (tiInstance t) x y
        field _ (Right InContainer{}) = error "TODO"
        field (x, y) (Left t) =
            ZipMatchField
                { zmfResult = [|Just $x|]
                , zmfConds = [[|$x == $y|]]
                , zmfContext = [[t|Eq $(pure t)|]]
                }
        embed t x y =
            ZipMatchField
                { zmfResult = [|zipMatch $x $y|]
                , zmfConds = []
                , zmfContext = [[t|ZipMatch $(pure t)|]]
                }

data ZipMatchField = ZipMatchField
    { zmfResult :: Q Exp
    , zmfConds :: [Q Exp]
    , zmfContext :: [Q Pred]
    }
