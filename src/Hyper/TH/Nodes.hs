{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'HNodes' instances via @TemplateHaskell@

module Hyper.TH.Nodes
    ( makeHNodes
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Data.Set as Set
import           Hyper.Class.Nodes
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'HNodes' instance
makeHNodes :: Name -> DecsQ
makeHNodes typeName = makeTypeInfo typeName >>= makeHNodesForType

makeHNodesForType :: TypeInfo -> DecsQ
makeHNodesForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''HNodes) (pure (tiInstance info)))
    [ tySynInstD ''HNodesConstraint
        (simplifyContext nodesConstraint <&> toTuple <&> TySynEqn [tiInstance info, VarT constraintVar])
    , dataInstD (pure []) ''HWitness
        [pure (tiInstance info), pure (VarT (mkName "node"))]
        Nothing (nodeOfCons <&> pure) []
    , InlineP 'hLiftConstraint Inline FunLike AllPhases & PragmaD & pure
    , funD 'hLiftConstraint (makeHLiftConstraints wit <&> pure)
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
                \x -> ConT ''HNodesConstraint `AppT` x `AppT` VarT constraintVar)
            <> Set.toList (tcOthers contents)

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._2 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer _ pat) = ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''HNodes `AppT` t]
        ctxForPat _ = []

makeHLiftConstraints :: NodeWitnesses -> [Clause]
makeHLiftConstraints wit
    | null clauses = [Clause [] (NormalB (LamCaseE [])) []]
    | otherwise = clauses
    where
        clauses = (nodeWitCtrs wit <&> liftNode) <> (embedWitCtrs wit <&> liftEmbed)
        liftNode x =
            Clause [ConP x []]
            (NormalB (VarE 'const `AppE` VarE 'id)) []
        liftEmbed x =
            Clause [ConP x [VarP witVar]]
            (NormalB (VarE 'hLiftConstraint `AppE` VarE witVar)) []
        witVar :: Name
        witVar = mkName "witness"
