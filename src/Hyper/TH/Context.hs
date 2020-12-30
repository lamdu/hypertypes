{-# LANGUAGE TemplateHaskell #-}

module Hyper.TH.Context
    ( makeHContext
    ) where

import qualified Control.Lens as Lens
import           Hyper.Class.Context (HContext(..))
import           Hyper.Class.Functor (HFunctor(..))
import           Hyper.Combinator.Func (HFunc(..), _HFunc)
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype (ConstructorVariant(..))

import           Hyper.Internal.Prelude

makeHContext :: Name -> DecsQ
makeHContext typeName = makeTypeInfo typeName >>= makeHContextForType

makeHContextForType :: TypeInfo -> DecsQ
makeHContextForType info =
    instanceD (simplifyContext (makeContext info)) [t|HContext $(pure (tiInstance info))|]
    [ InlineP 'hcontext Inline FunLike AllPhases & PragmaD & pure
    , funD 'hcontext (tiConstructors info <&> makeHContextCtr)
    ]
    <&> (:[])

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._3 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (GenEmbed t) = embed t
        ctxForPat (FlatEmbed x) = embed (tiInstance x)
        ctxForPat _ = []
        embed t = [ConT ''HContext `AppT` t, ConT ''HFunctor `AppT` t]

makeHContextCtr ::
    (Name, ConstructorVariant, [Either Type CtrTypePattern]) -> Q Clause
makeHContextCtr (cName, _, []) =
    clause [conP cName []] (normalB (conE cName)) []
makeHContextCtr (cName, RecordConstructor fieldNames, cFields) =
    clause [varWhole `asP` conP cName (cVars <&> varP)]
    (normalB (foldl appE (conE cName) (zipWith bodyFor cFields (zip fieldNames cVars)))) []
    where
        cVars =
            [(0 :: Int) ..] <&> show <&> ("_x" <>) <&> mkName
            & take (length cFields)
        bodyFor Left{} (_, v) = varE v
        bodyFor (Right Node{}) (f, v) =
            [|HFunc
                $(lamE [varP varField]
                    [|Lens.Const $(recUpdE (varE varWhole) [pure (f, VarE varField)])|])
                :*: $(varE v)|]
        bodyFor _ _ = fail "makeHContext only works for simple record fields"
        varWhole = mkName "_whole"
        varField = mkName "_field"
makeHContextCtr (cName, _, [cField]) =
    clause [conP cName [varP cVar]] (normalB (n `appE` bodyFor cField)) []
    where
        n = conE cName
        v = varE cVar
        bodyFor Left{} = v
        bodyFor (Right Node{}) = [|HFunc (Lens.Const . $n) :*: $v|]
        bodyFor (Right GenEmbed{}) = embed
        bodyFor (Right FlatEmbed{}) = embed
        bodyFor _ = fail "makeHContext only works for simple fields"
        embed =
            [|hmap
                (const (Lens._1 . _HFunc . Lens.mapped . Lens._Wrapped Lens.%~ $n))
                (hcontext $v)
            |]
        cVar = mkName "_c"
makeHContextCtr _ = fail "makeHContext: unsupported constructor"
