{-@ LIQUID "--reflection" @-}

{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}

module Bot where

-- import Proof

-- {-@
-- data Bot = Bot (contra :: {contra:Proof | False})
-- @-}
-- data Bot = Bot Proof

-- -- note that `absurd` cannot be reflected
-- absurd :: Bot -> a
-- absurd (Bot contra) = case contra of

-- {-@
-- data BotX a = BotX (contraX :: {contraX:a | False})
-- @-}
-- data BotX a = BotX a

-- -- note that `absurdX` ALSO cannot be reflected...
-- {-@
-- absurdX :: forall <p :: a -> Bool>. BotX a -> a
-- @-}
-- absurdX :: BotX a -> a
-- absurdX (BotX contraX) = case contraX of
