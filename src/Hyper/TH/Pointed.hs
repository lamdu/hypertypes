{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'HPointed' instances via @TemplateHaskell@

module Hyper.TH.Pointed
    ( makeHPointed
    ) where

import           Hyper.Class.Pointed
import           Hyper.TH.Internal.Utils
import           Control.Lens.Operators
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'HPointed' instance
makeHPointed :: Name -> DecsQ
makeHPointed typeName = makeTypeInfo typeName >>= makeHPointedForType

makeHPointedForType :: TypeInfo -> DecsQ
makeHPointedForType info =
    do
        cons <-
            case tiConstructors info of
            [x] -> pure x
            _ -> fail "makeHPointed only supports types with a single constructor"
        instanceD (simplifyContext (makeContext info)) (appT (conT ''HPointed) (pure (tiInstance info)))
            [ InlineP 'pureK Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureK [makePureKCtr info cons]
            ]
    <&> (:[])

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info >>= snd >>= ctxFor
    where
        ctxFor (Right x) = ctxForPat x
        ctxFor (Left x) = [ConT ''Monoid `AppT` x]
        ctxForPat (InContainer t pat) = (ConT ''Applicative `AppT` t) : ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''HPointed `AppT` t]
        ctxForPat _ = []

makePureKCtr :: TypeInfo -> (Name, [Either Type CtrTypePattern]) -> Q Clause
makePureKCtr typeInfo (cName, cFields) =
    traverse bodyFor cFields
    <&> foldl AppE (ConE cName)
    <&> NormalB
    <&> \x -> Clause [VarP varF] x []
    where
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = VarE 'mempty & pure
        bodyForPat (Node t) = VarE varF `AppE` nodeWit wit t & pure
        bodyForPat (FlatEmbed inner) =
            case tiConstructors inner of
            [(iName, iFields)] -> traverse bodyFor iFields <&> foldl AppE (ConE iName)
            _ -> fail "makeHPointed only supports embedded types with a single constructor"
        bodyForPat (GenEmbed t) =
            VarE 'pureK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))
            & pure
        bodyForPat (InContainer _ pat) =
            bodyForPat pat <&> AppE (VarE 'pure)
        varF = mkName "_f"
        (_, wit) = makeNodeOf typeInfo
