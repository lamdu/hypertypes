{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KPointed' instances via @TemplateHaskell@

module AST.TH.Pointed
    ( makeKPointed
    ) where

import           AST.Class.Pointed
import           AST.TH.Internal.Utils
import           Control.Lens.Operators
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'KPointed' instance
makeKPointed :: Name -> DecsQ
makeKPointed typeName = makeTypeInfo typeName >>= makeKPointedForType

makeKPointedForType :: TypeInfo -> DecsQ
makeKPointedForType info =
    do
        cons <-
            case tiConstructors info of
            [x] -> pure x
            _ -> fail "makeKPointed only supports types with a single constructor"
        instanceD (simplifyContext (makeContext info)) (appT (conT ''KPointed) (pure (tiInstance info)))
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
        ctxForPat (GenEmbed t) = [ConT ''KPointed `AppT` t]
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
            _ -> fail "makeKPointed only supports embedded types with a single constructor"
        bodyForPat (GenEmbed t) =
            VarE 'pureK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))
            & pure
        bodyForPat (InContainer _ pat) =
            bodyForPat pat <&> AppE (VarE 'pure)
        varF = mkName "_f"
        (_, wit) = makeNodeOf typeInfo
