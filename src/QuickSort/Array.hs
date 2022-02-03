{-@ LIQUID "--reflection" @-}

module QuickSort.Array where

-- import Proof
-- import Refined.Function

-- {-@
-- data Array m = Array
--   { pureArray :: forall a. a -> m a,
--     bindArray :: forall a b. m a -> (a -> m b) -> m b,
--     pureBindArray :: forall a b. a:a -> k:(a -> m b) ->
--       Equal (m b) {bindArray (pureArray a) k} {k a},
--     bindPureArray :: forall a. m:m a ->
--       Equal (m a) {bindArray m pureArray} {m},
--     assocArray :: forall a b c. m:m a -> k1:(a -> m b) -> k2:(b -> m c) ->
--       Equal (m c)
--         {bindArray (bindArray m k1) k2}
--         {bindArray m (kleisli_proto bindArray k1 k2)},
--     lengthArray :: Int,
--     positive_lengthArray :: {0 <= lengthArray},
--     readArray :: {i:Int | inBounds lengthArray i} -> m El,
--     writeArray :: {i:Int | inBounds lengthArray i} -> El -> m Unit
--   }
-- @-}
-- data Array m = Array
--   { pureArray :: forall a. a -> m a,
--     bindArray :: forall a b. m a -> (a -> m b) -> m b,
--     pureBindArray :: forall a b. a -> (a -> m b) -> Equal (m b),
--     bindPureArray :: forall a. m a -> Equal (m a),
--     assocArray :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> Equal (m c),
--     lengthArray :: Int,
--     positive_lengthArray :: Proof,
--     readArray :: Int -> m El,
--     writeArray :: Int -> El -> m Unit
--     -- TODO: 
--   }
