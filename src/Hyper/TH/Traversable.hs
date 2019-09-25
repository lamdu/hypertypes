{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KTraversable' and related instances via @TemplateHaskell@

module Hyper.TH.Traversable
    ( makeKTraversable
    , makeKTraversableAndFoldable
    , makeKTraversableAndBases
    , makeKTraversableApplyAndBases
    ) where

import           Hyper.Class.Traversable
import           Hyper.TH.Apply (makeKApplicativeBases)
import           Hyper.TH.Foldable (makeKFoldable)
import           Hyper.TH.Functor (makeKFunctor)
import           Hyper.TH.Internal.Utils
import           Hyper.TH.Nodes (makeKNodes)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate 'KTraversable' and 'Hyper.Class.Apply.KApply' instances along with all of their base classes:
-- 'Hyper.Class.Foldable.KFoldable', 'Hyper.Class.Functor.KFunctor',
-- 'Hyper.Class.Pointed.KPointed', and 'Hyper.Class.Nodes.KNodes'.
makeKTraversableApplyAndBases :: Name -> DecsQ
makeKTraversableApplyAndBases x =
    sequenceA
    [ makeKApplicativeBases x
    , makeKTraversableAndFoldable x
    ] <&> concat

-- | Generate a 'KTraversable' instance along with the instance of its base classes:
-- 'Hyper.Class.Foldable.KFoldable', 'Hyper.Class.Functor.KFunctor', and 'Hyper.Class.Nodes.KNodes'.
makeKTraversableAndBases :: Name -> DecsQ
makeKTraversableAndBases x =
    sequenceA
    [ makeKNodes x
    , makeKFunctor x
    , makeKTraversableAndFoldable x
    ] <&> concat

-- | Generate 'KTraversable' and 'Hyper.Class.Foldable.KFoldable' instances
makeKTraversableAndFoldable :: Name -> DecsQ
makeKTraversableAndFoldable x =
    sequenceA
    [ makeKFoldable x
    , makeKTraversable x
    ] <&> concat

-- | Generate a 'KTraversable' instance
makeKTraversable :: Name -> DecsQ
makeKTraversable typeName = makeTypeInfo typeName >>= makeKTraversableForType

makeKTraversableForType :: TypeInfo -> DecsQ
makeKTraversableForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KTraversable) (pure (tiInstance info)))
    [ InlineP 'sequenceK Inline FunLike AllPhases & PragmaD & pure
    , funD 'sequenceK (tiConstructors info <&> pure . uncurry makeCons)
    ]
    <&> (:[])

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._2 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer t pat) = (ConT ''Traversable `AppT` t) : ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''KTraversable `AppT` t]
        ctxForPat (FlatEmbed t) = [ConT ''KTraversable `AppT` tiInstance t]
        ctxForPat _ = []

makeCons ::
    Name -> [Either Type CtrTypePattern] -> Clause
makeCons cName cFields =
    Clause [consPat cName consVars] body []
    where
        body =
            consVars <&> f
            & applicativeStyle (ConE cName)
            & NormalB
        consVars = makeConstructorVars "x" cFields
        f (pat, name) = bodyFor pat `AppE` VarE name
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = VarE 'pure
        bodyForPat Node{} = VarE 'runContainedK
        bodyForPat FlatEmbed{} = VarE 'sequenceK
        bodyForPat GenEmbed{} = VarE 'sequenceK
        bodyForPat (InContainer _ pat) = VarE 'traverse `AppE` bodyForPat pat
