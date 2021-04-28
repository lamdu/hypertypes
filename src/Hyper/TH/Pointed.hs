{-# LANGUAGE TemplateHaskell #-}

-- | Generate 'HPointed' instances via @TemplateHaskell@

module Hyper.TH.Pointed
    ( makeHPointed
    ) where

import qualified Control.Lens as Lens
import           Hyper.Class.Pointed (HPointed(..))
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype (ConstructorVariant)

import           Hyper.Internal.Prelude

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
        instanceD (makeContext info >>= simplifyContext) [t|HPointed $(pure (tiInstance info))|]
            [ InlineP 'hpure Inline FunLike AllPhases & PragmaD & pure
            , funD 'hpure [makeHPureCtr info cons]
            ]
    <&> (:[])

makeContext :: TypeInfo -> Q [Pred]
makeContext info =
    tiConstructors info >>= (^. Lens._3) & traverse ctxFor <&> mconcat
    where
        ctxFor (Right x) = ctxForPat x
        ctxFor (Left x) = [t|Monoid $(pure x)|] <&> (:[])
        ctxForPat (InContainer t pat) = (:) <$> [t|Applicative $(pure t)|] <*> ctxForPat pat
        ctxForPat (GenEmbed t) = [t|HPointed $(pure t)|] <&> (:[])
        ctxForPat (FlatEmbed t) = makeContext t
        ctxForPat _ = pure []

makeHPureCtr :: TypeInfo -> (Name, ConstructorVariant, [Either Type CtrTypePattern]) -> Q Clause
makeHPureCtr typeInfo (cName, _, cFields) =
    clause [varP varF] (normalB (foldl appE (conE cName) (cFields <&> bodyFor))) []
    where
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = [|mempty|]
        f = varE varF
        bodyForPat (Node t) = [|$f $(nodeWit wit t)|]
        bodyForPat (FlatEmbed inner) =
            case tiConstructors inner of
            [(iName, _, iFields)] -> iFields <&> bodyFor & foldl appE (conE iName)
            _ -> fail "makeHPointed only supports embedded types with a single constructor"
        bodyForPat (GenEmbed t) = [|hpure ($f . $(embedWit wit t))|]
        bodyForPat (InContainer _ pat) = [|pure $(bodyForPat pat)|]
        varF = mkName "_f"
        (_, wit) = makeNodeOf typeInfo
