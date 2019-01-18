{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Class.ZipMatch.TH
    ( makeZipMatch, makeChildrenAndZipMatch
    ) where

import           AST.Class.Children.TH
import           AST.Class.ZipMatch (ZipMatch(..), Both(..))
import           Control.Lens.Operators
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeChildrenAndZipMatch :: Name -> DecsQ
makeChildrenAndZipMatch typeName =
    (<>)
    <$> makeChildren typeName
    <*> makeZipMatch typeName

makeZipMatch :: Name -> DecsQ
makeZipMatch typeName =
    do
        info <- D.reifyDatatype typeName
        (dst, var) <- parts info
        let ctrs = D.datatypeCons info <&> makeZipMatchCtr var
        instanceD
            (pure (ctrs >>= ccContext & Set.fromList & Set.toList))
            (appT (conT ''ZipMatch) (pure dst))
            [ InlineP 'zipMatch Inline FunLike AllPhases & PragmaD & pure
            , funD 'zipMatch
                ( (ctrs <&> pure . ccClause) ++ [pure tailClause]
                )
            ]
            <&> (:[])
    where
        tailClause = Clause [WildP, WildP] (NormalB (ConE 'Nothing)) []

makeZipMatchCtr :: Name -> D.ConstructorInfo -> CtrCase
makeZipMatchCtr var info =
    CtrCase
    { ccClause = Clause [con fst, con snd] body []
    , ccContext = fieldParts >>= zmfContext
    }
    where
        con f = ConP (D.constructorName info) (cVars <&> f <&> VarP)
        cVars =
            [0::Int ..] <&> show <&> (\n -> (mkName ('x':n), mkName ('y':n)))
            & take (length (D.constructorFields info))
        body
            | null checks = NormalB bodyExp
            | otherwise = GuardedB [(NormalG (foldl1 mkAnd checks), bodyExp)]
        checks = fieldParts >>= zmfConds
        mkAnd x y = InfixE (Just x) (VarE '(&&)) (Just y)
        fieldParts = zipWith field cVars (D.constructorFields info <&> matchType var)
        bodyExp = applicativeStyle (ConE (D.constructorName info)) (fieldParts <&> zmfResult)
        field (x, y) NodeFofX{} =
            ZipMatchField
            { zmfResult = ConE 'Just `AppE` (ConE 'Both `AppE` VarE x `AppE` VarE y)
            , zmfConds = []
            , zmfContext = []
            }
        field (x, y) (XofF t) =
            ZipMatchField
            { zmfResult = VarE 'zipMatch `AppE` VarE x `AppE` VarE y
            , zmfConds = []
            , zmfContext = [ConT ''ZipMatch `AppT` t | isPolymorphic t]
            }
        field _ Tof{} = error "TODO"
        field (x, y) (Other t) =
            ZipMatchField
            { zmfResult = ConE 'Just `AppE` VarE x
            , zmfConds = [InfixE (Just (VarE x)) (VarE '(==)) (Just (VarE y))]
            , zmfContext = [ConT ''Eq `AppT` t | isPolymorphic t]
            }

data ZipMatchField = ZipMatchField
    { zmfResult :: Exp
    , zmfConds :: [Exp]
    , zmfContext :: [Pred]
    }
