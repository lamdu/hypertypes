{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Class.Recursive.TH
    ( makeRecursive, makeChildrenRecursive
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Children.TH
import           AST.Class.Recursive (Recursive)
import           Control.Lens.Operators
import qualified Data.Set as Set
import           Language.Haskell.TH

import           Prelude.Compat

makeChildrenRecursive :: [Name] -> DecsQ
makeChildrenRecursive typeNames =
    do
        chldrn <- traverse makeChildren typeNames <&> concat
        typeInfos <- traverse makeTypeInfo typeNames
        let recCtx = typeInfos >>= childrenContext & Set.fromList & Set.toList
        recs <-
            case recCtx of
            [] -> traverse makeRecursive (findRecursives typeInfos)
            _ -> pure []
        pure (chldrn <> recs)

findRecursives :: [TypeInfo] -> [TypeInfo]
findRecursives infos
    | (infos <&> tiInstance) == (next <&> tiInstance) = infos
    | otherwise = findRecursives next
    where
        next = filter hasDeps infos
        hasDeps = all (`Set.member` cur) . Set.toList . tiChildren
        cur = Set.fromList (infos <&> tiInstance)

makeRecursive :: TypeInfo -> DecQ
makeRecursive info =
    instanceD (pure []) (conT ''Recursive `appT` conT ''Children `appT` pure (tiInstance info)) []
