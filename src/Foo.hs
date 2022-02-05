{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RankNTypes #-}

module Foo where

-- {-@
-- data M m = M
--   { pureM :: forall a <p :: a -> Bool>. a<p> -> m a<p>,
--     bindM :: forall a b <p :: b -> Bool>. m a -> (a -> m b<p>) -> m b<p>
--   }
-- @-}
-- data M m = M
--   { pureM :: forall a. a -> m a,
--     bindM :: forall a b. m a -> (a -> m b) -> m b
--   }

-- {-@ reflect constant @-}
-- {-@
-- constant :: forall a b <p :: a -> Bool>. a<p> -> b -> a<p>
-- @-}
-- constant :: a -> b -> a
-- constant a _ = a

-- -- {-@ reflect seqM @-}
-- {-@
-- seqM :: forall m a b <p :: b -> Bool>. M m -> m a -> m b<p> -> m b<p>
-- @-}
-- seqM :: forall m a b. M m -> m a -> m b -> m b
-- seqM iM ma mb = bindM iM ma (constant mb)

-- {-@
-- test :: iM:M m -> x:{Int | 0 <= x} -> m ({x:Int | 0 <= x})
-- @-}
-- test :: M m -> Int -> m Int
-- test iM x = seqM iM (pureM iM x) (pureM iM x)

{-@
data M m = M
  { pureM :: forall a. a -> m a,
    bindM :: forall a b. m a -> (a -> m b) -> m b
  }
@-}
data M m = M
  { pureM :: forall a. a -> m a,
    bindM :: forall a b. m a -> (a -> m b) -> m b
  }

{-@ reflect constant @-}
{-@
constant :: forall a b <p :: a -> Bool>. a<p> -> b -> a<p>
@-}
constant :: a -> b -> a
constant a _ = a

{-@ reflect seqM @-}
seqM :: forall m a b. M m -> m a -> m b -> m b
seqM iM ma mb = bindM iM ma (constant mb)

{-@
test :: iM:M m -> x:{Int | 0 <= x} -> m ({x:Int | 0 <= x})
@-}
test :: M m -> Int -> m Int
test iM x = seqM iM (pureM iM x) (pureM iM x)
