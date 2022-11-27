-- | A convinience module which re-exports common functionality of the hypertypes library
module Hyper (module X) where

import Data.Constraint as X (Constraint, Dict (..), withDict)
import Data.Functor.Const as X (Const (..))
import Data.Proxy as X (Proxy (..))
import GHC.Generics as X (Generic, (:*:) (..))
import Hyper.Class.Apply as X (HApplicative, HApply (..), liftH2)
import Hyper.Class.Foldable as X (HFoldable (..), hfoldMap, hfolded1, htraverse1_, htraverse_)
import Hyper.Class.Functor as X (HFunctor (..), hmapped1)
import Hyper.Class.HasPlain as X (HasHPlain (..))
import Hyper.Class.Nodes as X (HNodes (..), HWitness (..), (#*#), (#>), _HWitness)
import Hyper.Class.Pointed as X (HPointed (..))
import Hyper.Class.Recursive as X (RNodes, RTraversable, Recursively (..))
import Hyper.Class.Traversable as X (HTraversable (..), htraverse, htraverse1)
import Hyper.Combinator.ANode as X
import Hyper.Combinator.Ann as X
import Hyper.Combinator.Compose as X (HCompose (..), hcomposed, _HCompose)
import Hyper.Combinator.Flip as X
import Hyper.Combinator.Func as X
import Hyper.TH.Apply as X (makeHApplicativeBases)
import Hyper.TH.Context as X (makeHContext)
import Hyper.TH.HasPlain as X (makeHasHPlain)
import Hyper.TH.Morph as X (makeHMorph)
import Hyper.TH.Traversable as X (makeHTraversableAndBases, makeHTraversableApplyAndBases)
import Hyper.TH.ZipMatch as X (makeZipMatch)
import Hyper.Type as X
import Hyper.Type.Pure as X
