{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}

module Refined.Control.Monad where

import Proof
import Relation.Equality.Prop

{-@
class Dflt a where
  dflt :: a
@-}
class Dflt a where
  dflt :: a

{-@
lem :: forall a. (Eq a, Dflt a) => f:(a -> a) -> x:a -> {f x == x}
@-}
lem :: forall a. (Eq a, Dflt a) => (a -> a) -> a -> Proof
lem = undefined

-- class PreMonad m where
--   {-@
--   ret :: forall a. a -> m a
--   @-}
--   ret :: forall a. a -> m a

--   {-@
--   bnd :: forall a b. m a -> (a -> m b) -> m b
--   @-}
--   bnd :: forall a b. m a -> (a -> m b) -> m b

-- class Monad m where
--   {-@
--   ret :: forall a. a -> m a
--   @-}
--   ret :: forall a. a -> m a

--   {-@
--   bnd :: forall a b. m a -> (a -> m b) -> m b
--   @-}
--   bnd :: forall a b. m a -> (a -> m b) -> m b

--   {-@
--   idL :: forall a b. a:a -> k:(a -> m b) -> {bnd (ret a) k = k a}
--   @-}
--   idL :: forall a b. a -> (a -> m b) -> Proof

-- {-@
-- idL :: forall a b. a:a -> k:(a -> m b) -> EqP (m b) {bnd (ret a) k} {k a}
-- @-}
-- idL :: forall a b. a -> (a -> m b) -> EqualProp (m b)

-- class PreMonad m => Monad m where
-- {-@
-- idL :: forall a b. a:a -> k:(a -> m b) -> EqP (m b) {bnd (ret a) k} {k a}
-- @-}
-- idL :: forall a b. a -> (a -> m b) -> EqualProp (m b)
