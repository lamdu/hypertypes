-- | A convinience module which re-exports common basic functionality of `hypertypes`

module Hyper (module X) where

import Hyper.Class.Apply as X (KApply(..), KApplicative, liftK2)
import Hyper.Class.HasPlain as X (KHasPlain(..))
import Hyper.Class.Foldable as X
    ( KFoldable(..), foldMapK, traverseK_, traverseK1_
    )
import Hyper.Class.Functor as X (KFunctor(..), mappedK1)
import Hyper.Class.Nodes as X (KNodes(..), (#>), (#*#))
import Hyper.Class.Pointed as X (KPointed(..))
import Hyper.Class.Traversable as X (KTraversable(..), traverseK, traverseK1)
import Hyper.Type.Combinator.ANode as X
import Hyper.Type as X
import Hyper.Type.Ann as X (Ann(..), ann, annotations)
import Hyper.Type.Pure as X
import Hyper.Class.Recursive as X (Recursively(..), RNodes, RTraversable)
import Hyper.TH.Apply as X (makeKApplicativeBases)
import Hyper.TH.HasPlain as X (makeKHasPlain)
import Hyper.TH.Traversable as X (makeKTraversableApplyAndBases, makeKTraversableAndBases)
import Hyper.TH.ZipMatch as X (makeZipMatch)
import Data.Functor.Product.PolyKinds as X (Product(..))
