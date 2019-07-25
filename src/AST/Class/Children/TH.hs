{-# LANGUAGE NoImplicitPrelude, TemplateHaskellQuotes #-}

module AST.Class.Children.TH
    ( makeChildren
    , -- Internals for use in TH for sub-classes
      CtrCase(..)
    ) where

import           AST.Class.Children (Children(..))
import           AST.Internal.TH
import           Control.Lens.Operators
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeChildren :: Name -> DecsQ
makeChildren typeName = makeTypeInfo typeName >>= makeChildrenForType

makeChildrenForType :: TypeInfo -> DecsQ
makeChildrenForType info =
    instanceD (simplifyContext ctx) (appT (conT ''Children) (pure (tiInstance info)))
    [ tySynInstD ''ChildrenConstraint
        (pure (TySynEqn [tiInstance info, VarT constraintVar] childrenConstraint))
    , InlineP 'children Inline FunLike AllPhases & PragmaD & pure
    , funD 'children (tiCons info <&> pure . ccClause . makeChildrenCtr (tiVar info))
    ] <&> (:[])
    where
        contents = tiContents info
        ctx = childrenContext info
        childrenConstraint =
            (Set.toList (tcChildren contents) <&> (VarT constraintVar `AppT`))
            <> (Set.toList (tcEmbeds contents) <&>
                \x -> ConT ''ChildrenConstraint `AppT` x `AppT` VarT constraintVar)
            <> Set.toList (tcOthers contents)
            & toTuple

constraintVar :: Name
constraintVar = mkName "constraint"

childrenContext :: TypeInfo -> [Pred]
childrenContext info =
    tiCons info <&> makeChildrenCtr (tiVar info) >>= ccContext

makeChildrenCtr :: Name -> D.ConstructorInfo -> CtrCase
makeChildrenCtr var info =
    CtrCase
    { ccClause =
        Clause
        [VarP proxy, VarP func, ConP (D.constructorName info) (cVars <&> VarP)]
        (NormalB body) []
    , ccContext = pats >>= ctxForPat
    }
    where
        proxy = mkName "_p"
        func = mkName "_f"
        cVars =
            [0::Int ..] <&> show <&> ('x':) <&> mkName
            & take (length (D.constructorFields info))
        body =
            zipWith AppE
            (pats <&> bodyForPat)
            (cVars <&> VarE)
            & applicativeStyle (ConE (D.constructorName info))
        pats = D.constructorFields info <&> matchType var
        bodyForPat NodeFofX{} = VarE func
        bodyForPat XofF{} = VarE 'children `AppE` VarE proxy `AppE` VarE func
        bodyForPat (Tof _ pat) = VarE 'traverse `AppE` bodyForPat pat
        bodyForPat Other{} = VarE 'pure
        ctxForPat (Tof t pat) = (ConT ''Traversable `AppT` t) : ctxForPat pat
        ctxForPat (XofF t) = [ConT ''Children `AppT` t]
        ctxForPat _ = []

data CtrCase =
    CtrCase
    { ccClause :: Clause
    , ccContext :: [Pred]
    }
