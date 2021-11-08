module QuickSort.Monadic where

-- Int

{-@ reflect add1 @-}
add1 :: Int -> Int
add1 x = x + 1

{-@ reflect sub1 @-}
sub1 :: Int -> Int
sub1 x = x - 1

-- types

{-@
data List a <p :: a -> a -> Bool> = Nil | Cons {hd::a, tl::List (a<p hd>)}
@-}
data List a = Nil | Cons a (List a)

{-@ measure lng @-}
lng :: List a -> Int
lng Nil = 0
lng (Cons _ xs) = 1 + lng xs

{-@
type ListI = List Int
@-}
type ListI = List Int

{-@
type ListIOrd = List<{\h v -> h <= v}> Int
@-}
type ListIOrd = List Int

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
  Get :: Arr ListI
@-}
data Arr :: * -> * where
  Ret :: a -> Arr a
  Bnd :: Arr a -> (a -> Arr b) -> Arr b
  Red :: Ix -> Arr Int
  Wrt :: Ix -> Int -> Arr ()
  Get :: Arr ListI

ret :: a -> Arr a
ret = Ret

bnd :: Arr a -> (a -> Arr b) -> Arr b
bnd = Bnd

red :: Ix -> Arr Int
red = Red

{-@
reds :: Ix -> {n:Int | 0 <= n} -> Arr ListI / [n]
@-}
reds :: Ix -> Int -> Arr ListI
reds i n =
  if n == 0
    then ret Nil
    else
      red i `bnd` \x ->
        reds (add1 i) (sub1 n) `bnd` \xs ->
          ret (Cons x xs)

wrt :: Ix -> Int -> Arr ()
wrt = Wrt

wrts :: Ix -> ListI -> Arr ()
wrts i Nil = ret ()
wrts i (Cons x xs) = wrt i x `thn` wrts (add1 i) xs

get :: Arr ListI
get = Get

thn :: Arr a -> Arr b -> Arr b
thn m1 m2 = Bnd m1 (\_ -> m2)

redList :: ListI -> Ix -> Maybe Int
redList Nil _ = Nothing
redList (Cons x xs) i =
  if i == 0
    then Just x
    else redList xs (sub1 i)

wrtList :: ListI -> Ix -> Int -> Maybe ListI
wrtList Nil _ _ = Nothing
wrtList (Cons x xs) i y =
  if i == 0
    then Just (Cons y xs)
    else case wrtList xs (sub1 i) y of
      Just xs' -> Just (Cons x xs')
      Nothing -> Nothing

-- failure conditions:
-- • read out of bounds
-- • write out of bounds
-- • throw error (via Err)
{-@ lazy runArr @-}
runArr :: Arr a -> ListI -> Maybe (a, ListI)
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

-- swap

-- swaps the values at indices i and j
swap :: Ix -> Ix -> Arr ()
swap i j = red i `bnd` \x -> red j `bnd` \y -> wrt i y `thn` wrt j x

-- quicksort

quicksort :: Arr ()
quicksort =
  get `bnd` \xs ->
    quicksort_aux 0 (sub1 (lng xs))

-- always chooses i0 as the pivot index `ip`
{-@ lazy quicksort_aux @-}
quicksort_aux :: Ix -> Ix -> Arr ()
quicksort_aux i0 i1 =
  partition i0 i1 0 `bnd` \i ->
    quicksort_aux i0 (sub1 i) `bnd` \_ ->
      quicksort_aux (add1 i) i1

-- partition

partition :: Ix -> Ix -> Ix -> Arr Int
partition i0 i1 ip =
  swap i0 ip `bnd` \_ ->
    red i0 `bnd` \p ->
      partition_iter i1 p (add1 i0) (add1 i0) `bnd` \i ->
        swap i0 (sub1 i) `bnd` \_ ->
          ret (sub1 i)

{-@ lazy partition_iter @-}
{-@
partition_iter :: i1:Ix -> p:Int -> i:Ix -> j:Ix -> Arr Ix / [j - i1]
@-}
partition_iter :: Ix -> Int -> Ix -> Ix -> Arr Ix
partition_iter i1 p i j =
  if j <= i1
    then
      red j `bnd` \x ->
        if x <= p
          then swap i j `thn` partition_iter i1 p (add1 i) (add1 j)
          else partition_iter i1 p i (add1 j)
    else ret i

-- runQuicksort

runQuicksort :: ListI -> Maybe ListI
runQuicksort xs = case runArr quicksort xs of
  Just (_, xs') -> Just xs'
  Nothing -> Nothing
