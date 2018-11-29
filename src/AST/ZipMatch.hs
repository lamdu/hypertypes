{-# LANGUAGE NoImplicitPrelude, RankNTypes, FlexibleContexts, ConstraintKinds #-}

module AST.ZipMatch
    ( ZipMatch(..)
    , zipMatch_
    ) where

import           AST (Node, Children(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Except (MonadError(..))
import           Data.Functor.Const (Const(..))
import           Data.Proxy (Proxy)

import           Prelude.Compat

class Children expr => ZipMatch expr where
    zipMatch ::
        (MonadError () m, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Node a child -> Node b child -> m (Node c child)) ->
        expr a -> expr b -> m (expr c)

zipMatch_ ::
    (ZipMatch expr, MonadError () m, ChildrenConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Node a child -> Node b child -> m ()) ->
    expr a -> expr b -> m ()
zipMatch_ p f x y =
    () <$ zipMatchH p f x y
    where
        zipMatchH ::
            (ZipMatch expr, MonadError () m, ChildrenConstraint expr constraint) =>
            Proxy constraint ->
            (forall child. constraint child => Node a child -> Node b child -> m ()) ->
            expr a -> expr b -> m (expr (Const ()))
        zipMatchH p' f' =
            zipMatch p' (f' <&> Lens.mapped . Lens.mapped .~ Const ())
