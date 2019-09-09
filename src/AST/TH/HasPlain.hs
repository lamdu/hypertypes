{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.HasPlain
    ( makeKHasPlain
    ) where

import           AST.Class.HasPlain
import           AST.Knot.Pure (_Pure)
import           AST.TH.Internal.Utils
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

-- | Generate a 'KHasPlain' instance
makeKHasPlain :: [Name] -> DecsQ
makeKHasPlain = traverse makeOne

makeOne :: Name -> Q Dec
makeOne typeName = makeTypeInfo typeName >>= makeKHasPlainForType

makeKHasPlainForType :: TypeInfo -> Q Dec
makeKHasPlainForType info =
    traverse (makeCtr (tiVar info)) (tiCons info)
    <&>
    \ctrs ->
    InstanceD Nothing [] (ConT ''KHasPlain `AppT` tiInstance info)
    [ DataInstD [] ''KPlain [tiInstance info] Nothing (ctrs <&> (^. Lens._1))
        [DerivClause (Just StockStrategy) [ConT ''Eq, ConT ''Ord, ConT ''Show]]
    , FunD 'kPlain
        [ Clause []
            ( NormalB
                (InfixE
                    (Just (VarE 'Lens.iso `AppE` VarE fromPlain `AppE` VarE toPlain))
                    (VarE '(.))
                    (Just (VarE 'Lens.from `AppE` VarE '_Pure))
                )
            )
            [ FunD toPlain (ctrs <&> (^. Lens._2))
            , FunD fromPlain (ctrs <&> (^. Lens._3))
            ]
        ]
    ]
    where
        toPlain = mkName "toPlain"
        fromPlain = mkName "fromPlain"

makeCtr :: Name -> D.ConstructorInfo -> Q (Con, Clause, Clause)
makeCtr knot info =
    (,,)
    <$> ( traverse dataForPat pats
            <&> Lens.mapped %~ (Bang NoSourceUnpackedness NoSourceStrictness, )
            <&> NormalC pcon
        )
    <*> ( traverse toPlainForPat pats
            <&> (\xs -> zipWith AppE xs (cVars <&> VarE))
            <&> foldl AppE (ConE pcon)
            <&> NormalB
            <&> \x -> Clause [ConP (D.constructorName info) (cVars <&> VarP)] x []
        )
    <*> ( traverse fromPlainForPat pats
            <&> (\xs -> zipWith AppE xs (cVars <&> VarE))
            <&> foldl AppE (ConE (D.constructorName info))
            <&> NormalB
            <&> \x -> Clause [ConP pcon (cVars <&> VarP)] x []
        )
    where
        pats = D.constructorFields info <&> matchType knot
        pcon =
            D.constructorName info
            & show & reverse & takeWhile (/= '.') & reverse
            & (<> "P") & mkName
        dataForPat (NodeFofX x) = ConT ''KPlain `AppT` x & pure
        dataForPat (Other t) = pure t
        dataForPat _ = fail "makeKHasPlain doesn't support this pattern (TODO)"
        toPlainForPat NodeFofX{} = InfixE (Just (VarE 'kPlain)) (VarE '(#)) Nothing & pure
        toPlainForPat Other{} = VarE 'id & pure
        toPlainForPat _ = fail "makeKHasPlain doesn't support this pattern (TODO)"
        fromPlainForPat NodeFofX{} = InfixE Nothing (VarE '(^.)) (Just (VarE 'kPlain)) & pure
        fromPlainForPat Other{} = VarE 'id & pure
        fromPlainForPat _ = fail "makeKHasPlain doesn't support this pattern (TODO)"
        cVars =
            [0::Int ..] <&> show <&> ('x':) <&> mkName
            & take (length (D.constructorFields info))
