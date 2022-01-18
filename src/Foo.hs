{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}

module Foo where

class C t where
  {-@
  f :: {t:t | t <= 10} -> t
  @-}
  f :: t -> t

instance C Bool where
  f x = x

{-@
lem :: {f True = True}
@-}
lem :: ()
lem = ()

{-@ reflect g @-}
g :: C t => t -> t
g t = f (f t)

-- class C t where
--   {-@
--   f :: t -> t
--   @-}
--   f :: t -> t

--   {-@ law :: x:t -> {f x == f (f x)} @-}
--   law :: t -> ()

-- {-@
-- lem :: C t => x:t -> {f x = f (f x)}
-- @-}
-- lem :: C t => t -> ()
-- lem x = law x
