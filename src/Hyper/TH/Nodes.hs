{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KNodes' instances via @TemplateHaskell@

module Hyper.TH.Nodes
    ( makeKNodes
    ) where

import           Hyper.Class.Nodes
import           Hyper.TH.Internal.Utils
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Data.Set as Set
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'KNodes' instance
makeKNodes :: Name -> DecsQ
makeKNodes typeName = makeTypeInfo typeName >>= makeKNodesForType

makeKNodesForType :: TypeInfo -> DecsQ
makeKNodesForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KNodes) (pure (tiInstance info)))
    [ tySynInstD ''KNodesConstraint
        (simplifyContext nodesConstraint <&> toTuple <&> TySynEqn [tiInstance info, VarT constraintVar])
    , dataInstD (pure []) ''KWitness
        [pure (tiInstance info), pure (VarT (mkName "node"))]
        Nothing (nodeOfCons <&> pure) []
    , InlineP 'kLiftConstraint Inline FunLike AllPhases & PragmaD & pure
    , funD 'kLiftConstraint (makeKLiftConstraints wit <&> pure)
    ]
    <&> (:[])
    where
        (nodeOfCons, wit) = makeNodeOf info
        constraintVar :: Name
        constraintVar = mkName "constraint"
        contents = childrenTypes info
        nodesConstraint =
            (Set.toList (tcChildren contents) <&> (VarT constraintVar `AppT`))
            <> (Set.toList (tcEmbeds contents) <&>
                \x -> ConT ''KNodesConstraint `AppT` x `AppT` VarT constraintVar)
            <> Set.toList (tcOthers contents)

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._2 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer _ pat) = ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''KNodes `AppT` t]
        ctxForPat _ = []

makeKLiftConstraints :: NodeWitnesses -> [Clause]
makeKLiftConstraints wit
    | null clauses = [Clause [] (NormalB (LamCaseE [])) []]
    | otherwise = clauses
    where
        clauses = (nodeWitCtrs wit <&> liftNode) <> (embedWitCtrs wit <&> liftEmbed)
        liftNode x =
            Clause [ConP x []]
            (NormalB (VarE 'const `AppE` VarE 'id)) []
        liftEmbed x =
            Clause [ConP x [VarP witVar]]
            (NormalB (VarE 'kLiftConstraint `AppE` VarE witVar)) []
        witVar :: Name
        witVar = mkName "witness"
