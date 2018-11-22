{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}

import Control.Lens
import Data.Tree.Diverse

data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)

deriving instance (Show (f (Typ f)), Show (Row f)) => Show (Typ f)
deriving instance (Show (f (Typ f)), Show (f (Row f))) => Show (Row f)

typ :: Node Identity Typ
typ =
    Identity REmpty
    & RExtend "hello" (Identity TInt) & TRow & Identity
    & TFun (Identity TInt) & Identity

main :: IO ()
main =
    do
        putStrLn ""
        print typ
