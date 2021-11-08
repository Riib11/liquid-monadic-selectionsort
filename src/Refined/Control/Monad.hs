{-@ LIQUID "--typeclass" @-}

module Refined.Control.Monad where

class F a where
  {-@ f :: a -> Bool @-}
  f :: a -> Bool

{-@
class F a => G a where
  g :: x:a -> {f x == True}
@-}
class F a => G a where
  g :: a -> ()

-- import Relation.Equality.Prop

-- {-@
-- class PreMnd m where
--   ret :: forall a. a -> m a
--   bnd :: forall a b. m a -> (a -> m b) -> m b
-- @-}
-- class PreMnd m where
--   ret :: forall a. a -> m a
--   bnd :: forall a b. m a -> (a -> m b) -> m b

-- {-@
-- class PreMnd m => Mnd m where
--   idL :: forall a b. a:a -> k:(a -> m b) -> EqP (m b) {bnd (ret a) k} {k a}
-- @-}
-- class PreMnd m => Mnd m where
--   idL :: forall a b. a -> (a -> m b) -> EqualProp (m b)
