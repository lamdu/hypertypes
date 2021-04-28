{-# LANGUAGE TemplateHaskell #-}

-- | Generate 'HTraversable' and related instances via @TemplateHaskell@

module Hyper.TH.Traversable
    ( makeHTraversable
    , makeHTraversableAndFoldable
    , makeHTraversableAndBases
    , makeHTraversableApplyAndBases
    ) where

import qualified Control.Lens as Lens
import           Hyper.Class.Traversable (HTraversable(..), ContainedH(..))
import           Hyper.TH.Apply (makeHApplicativeBases)
import           Hyper.TH.Foldable (makeHFoldable)
import           Hyper.TH.Functor (makeHFunctor)
import           Hyper.TH.Internal.Utils
import           Hyper.TH.Nodes (makeHNodes)
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype (ConstructorVariant)

import           Hyper.Internal.Prelude

-- | Generate 'HTraversable' and 'Hyper.Class.Apply.HApply' instances along with all of their base classes:
-- 'Hyper.Class.Foldable.HFoldable', 'Hyper.Class.Functor.HFunctor',
-- 'Hyper.Class.Pointed.HPointed', and 'Hyper.Class.Nodes.HNodes'.
makeHTraversableApplyAndBases :: Name -> DecsQ
makeHTraversableApplyAndBases x =
    sequenceA
    [ makeHApplicativeBases x
    , makeHTraversableAndFoldable x
    ] <&> concat

-- | Generate a 'HTraversable' instance along with the instance of its base classes:
-- 'Hyper.Class.Foldable.HFoldable', 'Hyper.Class.Functor.HFunctor', and 'Hyper.Class.Nodes.HNodes'.
makeHTraversableAndBases :: Name -> DecsQ
makeHTraversableAndBases x =
    sequenceA
    [ makeHNodes x
    , makeHFunctor x
    , makeHTraversableAndFoldable x
    ] <&> concat

-- | Generate 'HTraversable' and 'Hyper.Class.Foldable.HFoldable' instances
makeHTraversableAndFoldable :: Name -> DecsQ
makeHTraversableAndFoldable x =
    sequenceA
    [ makeHFoldable x
    , makeHTraversable x
    ] <&> concat

-- | Generate a 'HTraversable' instance
makeHTraversable :: Name -> DecsQ
makeHTraversable typeName = makeTypeInfo typeName >>= makeHTraversableForType

makeHTraversableForType :: TypeInfo -> DecsQ
makeHTraversableForType info =
    instanceD (makeContext info >>= simplifyContext) [t|HTraversable $(pure (tiInstance info))|]
    [ InlineP 'hsequence Inline FunLike AllPhases & PragmaD & pure
    , funD 'hsequence (tiConstructors info <&> makeCons)
    ]
    <&> (:[])

makeContext :: TypeInfo -> Q [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._3 . traverse . Lens._Right
    & traverse ctxForPat <&> mconcat
    where
        ctxForPat (InContainer t pat) = (:) <$> [t|Traversable $(pure t)|] <*> ctxForPat pat
        ctxForPat (GenEmbed t) = [t|HTraversable $(pure t)|] <&> (:[])
        ctxForPat (FlatEmbed t) = makeContext t
        ctxForPat _ = pure []

makeCons ::
    (Name, ConstructorVariant, [Either Type CtrTypePattern]) -> ClauseQ
makeCons (cName, _, cFields) =
    clause [consPat cName consVars] body []
    where
        body =
            consVars <&> f
            & applicativeStyle (conE cName)
            & normalB
        consVars = makeConstructorVars "x" cFields
        f (pat, name) = bodyFor pat `appE` varE name
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = [|pure|]
        bodyForPat Node{} = [|runContainedH|]
        bodyForPat FlatEmbed{} = [|hsequence|]
        bodyForPat GenEmbed{} = [|hsequence|]
        bodyForPat (InContainer _ pat) = [|traverse $(bodyForPat pat)|]
