{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.ZipMatch
    ( makeZipMatch
    ) where

import           AST.Class.ZipMatch (ZipMatch(..))
import           AST.TH.Internal
import           Control.Lens.Operators
import           Data.Functor.Product.PolyKinds (Product(..))
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeZipMatch :: Name -> DecsQ
makeZipMatch typeName =
    do
        info <- D.reifyDatatype typeName
        (dst, var) <- parts info
        let ctrs = D.datatypeCons info <&> makeZipMatchCtr var
        instanceD
            (simplifyContext (ctrs >>= ccContext))
            (appT (conT ''ZipMatch) (pure dst))
            [ InlineP 'zipMatch Inline FunLike AllPhases & PragmaD & pure
            , funD 'zipMatch
                ( (ctrs <&> pure . ccClause) ++ [pure tailClause]
                )
            ]
            <&> (:[])
    where
        tailClause = Clause [WildP, WildP] (NormalB (ConE 'Nothing)) []

data CtrCase =
    CtrCase
    { ccClause :: Clause
    , ccContext :: [Pred]
    }

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
            { zmfResult = ConE 'Just `AppE` (ConE 'Pair `AppE` VarE x `AppE` VarE y)
            , zmfConds = []
            , zmfContext = []
            }
        field (x, y) (XofF t) =
            ZipMatchField
            { zmfResult = VarE 'zipMatch `AppE` VarE x `AppE` VarE y
            , zmfConds = []
            , zmfContext = [ConT ''ZipMatch `AppT` t]
            }
        field _ Tof{} = error "TODO"
        field (x, y) (Other t) =
            ZipMatchField
            { zmfResult = ConE 'Just `AppE` VarE x
            , zmfConds = [InfixE (Just (VarE x)) (VarE '(==)) (Just (VarE y))]
            , zmfContext = [ConT ''Eq `AppT` t]
            }

data ZipMatchField = ZipMatchField
    { zmfResult :: Exp
    , zmfConds :: [Exp]
    , zmfContext :: [Pred]
    }
