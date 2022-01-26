{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}

module Foo where

-- {-@ type Proof = () @-}
-- type Proof = ()

-- {-@
-- type Equal a X Y = pr:(a -> Bool) -> {pr X = pr Y}
-- @-}
-- type Equal a = (a -> Bool) -> Proof

-- {-@ type Ix = Int @-}
-- type Ix = Int

-- {-@ type El = Int @-}
-- type El = Int

-- {-@ reflect inBounds @-}
-- inBounds :: forall m. Array m => Ix -> m Bool
-- inBounds i = bindArray (len :: Array m => m Ix) (inBounds_aux i)

-- {-@ reflect inBounds_aux @-}
-- inBounds_aux :: forall m. Array m => Ix -> Ix -> m Bool
-- inBounds_aux i l = pureArray (i < l)

-- class Array (m :: * -> *) where
--   {-@ pureArray :: forall a. a -> m a @-}
--   pureArray :: forall a. a -> m a

--   {-@ bindArray :: forall a b. m a -> (a -> m b) -> m b @-}
--   bindArray :: forall a b. m a -> (a -> m b) -> m b

--   {-@ len :: m Ix @-}
--   len :: m Ix
