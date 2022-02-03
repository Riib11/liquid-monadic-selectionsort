module Foo where

-- {-@ inline impossible @-}
-- {-@ impossible :: {_:a | False} -> a @-}
-- impossible :: a -> a
-- impossible a = a

-- class Array (m :: * -> *) where
--   {-@
--   readArray :: {i:Int | 0 <= i} -> m Int
--   @-}
--   readArray :: Int -> m Int
