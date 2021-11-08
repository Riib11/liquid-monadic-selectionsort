module Imperative.ArrayOld where

import Proof
import Refined.Data.Int
import Refined.Data.List

{-@
type Ix = Int
@-}
type Ix = Int

-- Arr

-- Algebraic effects for a monadic (stateful) array.
{-@
data Arr :: * -> * where
  Ret :: a -> Arr a
  Bnd :: Arr a -> (a -> Arr b) -> Arr b
  Red :: Ix -> Arr Int
  Wrt :: Ix -> Int -> Arr ()
  Get :: Arr List
@-}
data Arr :: * -> * where
  Ret :: a -> Arr a
  Bnd :: Arr a -> (a -> Arr b) -> Arr b
  Red :: Ix -> Arr Int
  Wrt :: Ix -> Int -> Arr ()
  Get :: Arr List

ret :: a -> Arr a
ret = Ret

bnd :: Arr a -> (a -> Arr b) -> Arr b
bnd = Bnd

red :: Ix -> Arr Int
red = Red

{-@
reds :: Ix -> {n:Int | 0 <= n} -> Arr List / [n]
@-}
reds :: Ix -> Int -> Arr List
reds i n =
  if n == 0
    then ret Nil
    else
      red i `bnd` \x ->
        reds (add1 i) (sub1 n) `bnd` \xs ->
          ret (Cons x xs)

wrt :: Ix -> Int -> Arr ()
wrt = Wrt

wrts :: Ix -> List -> Arr ()
wrts i Nil = ret ()
wrts i (Cons x xs) = wrt i x `thn` wrts (add1 i) xs

get :: Arr List
get = Get

thn :: Arr a -> Arr b -> Arr b
thn m1 m2 = Bnd m1 (\_ -> m2)

-- runArr

-- failure conditions:
-- • read out of bounds
-- • write out of bounds
-- • throw error (via Err)
{-@ lazy runArr @-}
runArr :: Arr a -> List -> Maybe (a, List)
runArr (Ret a) xs = Just (a, xs)
runArr (Bnd m k) xs =
  case runArr m xs of
    Just (a, xs') -> runArr (k a) xs'
    Nothing -> Nothing
runArr (Red i) xs =
  case redList xs i of
    Just x -> Just (x, xs)
    Nothing -> Nothing
runArr (Wrt i x) xs =
  case wrtList xs i x of
    Just xs' -> Just ((), xs')
    Nothing -> Nothing
runArr (Get) xs = Just (xs, xs)

redList :: List -> Ix -> Maybe Int
redList Nil _ = Nothing
redList (Cons x xs) i =
  if i == 0
    then Just x
    else redList xs (sub1 i)

wrtList :: List -> Ix -> Int -> Maybe List
wrtList Nil _ _ = Nothing
wrtList (Cons x xs) i y =
  if i == 0
    then Just (Cons y xs)
    else case wrtList xs (sub1 i) y of
      Just xs' -> Just (Cons x xs')
      Nothing -> Nothing

-- swap

-- swaps the values at indices i and j
swap :: Ix -> Ix -> Arr ()
swap i j = red i `bnd` \x -> red j `bnd` \y -> wrt i y `thn` wrt j x

-- checkInBounds

checkInBounds :: Int -> Arr Bool
checkInBounds i = get `bnd` \xs -> ret (0 <= i && i < lng xs)

-- getLng

getLng :: Arr Int
getLng = get `bnd` \xs -> ret (lng xs)
