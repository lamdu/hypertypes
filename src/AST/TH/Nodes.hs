{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Nodes
    ( makeKNodes
    ) where

import           AST.Class.Nodes
import           AST.TH.Internal.Utils
import           Control.Lens.Operators
import           Data.Constraint (Dict(..))
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

-- | Generate a 'KNodes' instance
makeKNodes :: Name -> DecsQ
makeKNodes typeName = makeTypeInfo typeName >>= makeKNodesForType

makeKNodesForType :: TypeInfo -> DecsQ
makeKNodesForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KNodes) (pure (tiInstance info)))
    [ tySynInstD ''NodesConstraint
        (simplifyContext nodesConstraint <&> toTuple <&> TySynEqn [tiInstance info, VarT constraintVar])
    , InlineP 'kCombineConstraints Inline FunLike AllPhases & PragmaD & pure
    , funD 'kCombineConstraints [pure (Clause [WildP] (NormalB (ConE 'Dict)) [])]
    ]
    <&> (:[])
    where
        constraintVar :: Name
        constraintVar = mkName "constraint"
        contents = tiContents info
        nodesConstraint =
            (Set.toList (tcChildren contents) <&> (VarT constraintVar `AppT`))
            <> (Set.toList (tcEmbeds contents) <&>
                \x -> ConT ''NodesConstraint `AppT` x `AppT` VarT constraintVar)
            <> Set.toList (tcOthers contents)

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (Tof _ pat) = ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KNodes `AppT` t]
        ctxForPat _ = []
