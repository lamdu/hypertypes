-- | A convinience module which re-exports common basic functionality of `syntax-tree`

module AST (module X) where

import AST.Class.Apply as X (KApply(..), KApplicative, liftK2)
import AST.Class.HasPlain as X (KHasPlain(..))
import AST.Class.Foldable as X
    ( KFoldable(..), foldMapK, traverseK_, traverseK1_
    )
import AST.Class.Functor as X (KFunctor(..), mappedK1)
import AST.Class.Nodes as X (KNodes(..), (#>), (#*#))
import AST.Class.Pointed as X (KPointed(..))
import AST.Class.Traversable as X (KTraversable(..), traverseK, traverseK1)
import AST.Combinator.ANode as X
import AST.Knot as X
import AST.Knot.Ann as X (Ann(..), ann, annotations)
import AST.Knot.Pure as X
import AST.Class.Recursive as X (Recursively(..), RNodes, RTraversable)
import AST.TH.Apply as X (makeKApplicativeBases)
import AST.TH.HasPlain as X (makeKHasPlain)
import AST.TH.Traversable as X (makeKTraversableApplyAndBases, makeKTraversableAndBases)
import AST.TH.ZipMatch as X (makeZipMatch)
import Data.Functor.Product.PolyKinds as X (Product(..))
