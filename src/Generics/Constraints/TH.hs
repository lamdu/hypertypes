{-# LANGUAGE TemplateHaskellQuotes #-}

module Generics.Constraints.TH
    ( makeDeriving, makeInstance
    ) where

import           Control.Lens.Operators
import           Generics.Constraints (Constraints)
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeDeriving :: Name -> Name -> DecsQ
makeDeriving = makeCommon (StandaloneDerivD Nothing)

makeInstance :: Name -> Name -> DecsQ
makeInstance = makeCommon (\c i -> InstanceD Nothing c i [])

makeCommon :: ([Type] -> Type -> Dec) -> Name -> Name -> DecsQ
makeCommon f clsName typName =
    D.reifyDatatype typName <&> r
    where
        r info =
            [ f [ConT ''Constraints `AppT` typ `AppT` ConT clsName] (ConT clsName `AppT` typ)
            ]
            where
                typ = foldl AppT (ConT typName) (D.datatypeVars info <&> D.tvName <&> VarT)
