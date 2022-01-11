{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--typeclass" @-}

module QuickSort.MonadicV6 where

import Proof
-- import Relation.Equality.Prop

import Refined.Data.Int
import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz

-- |
-- = Natural Number

-- Nat

{-@
data Nat = Zero | Suc Nat
@-}
data Nat = Zero | Suc Nat
  deriving (Show)

-- :+

type family m :+ n where
  Zero :+ n = n
  Suc m :+ n = Suc (m :+ n)

-- SNat

{-@
data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSuc :: SNat n -> SNat (Suc n)
@-}
data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSuc :: SNat n -> SNat (Suc n)

-- Ix

{-@
data Ix :: Nat -> * where
  IxZero :: Ix (Suc n)
  IxSuc :: Ix n -> Ix (Suc n)
@-}
data Ix :: Nat -> * where
  IxZero :: Ix (Suc n)
  IxSuc :: Ix n -> Ix (Suc n)

instance Eq (Ix n) where
  IxZero == IxZero = True
  IxSuc i == IxSuc j = i == j

{-@ reflect leIx @-}
leIx :: Ix n -> Ix n -> Bool
leIx IxZero _ = True
leIx (IxSuc i) IxZero = False
leIx (IxSuc i) (IxSuc j) = leIx i j

{-@ reflect ltIx @-}
ltIx :: Ix n -> Ix n -> Bool
ltIx IxZero IxZero = False
ltIx IxZero (IxSuc j) = True
ltIx (IxSuc i) IxZero = False
ltIx (IxSuc i) (IxSuc j) = ltIx i j

maxIx :: SNat (Suc n) -> Ix (Suc n)
maxIx (SSuc SZero) = IxZero

{-@ reflect isMaxIx @-}
isMaxIx :: SNat n -> Ix n -> Bool
isMaxIx SZero i = True
isMaxIx (SSuc SZero) IxZero = True
isMaxIx (SSuc (SSuc SZero)) IxZero = False
isMaxIx (SSuc (SSuc SZero)) (IxSuc IxZero) = False
isMaxIx (SSuc n@(SSuc _)) IxZero = False
isMaxIx (SSuc n@(SSuc _)) (IxSuc i) = isMaxIx n i

{-@ reflect add1Ix @-}
add1Ix :: SNat n -> Ix n -> Ix n
add1Ix SZero i = i
add1Ix (SSuc SZero) IxZero = IxZero
add1Ix (SSuc (SSuc SZero)) IxZero = IxSuc IxZero
add1Ix (SSuc (SSuc SZero)) (IxSuc IxZero) = IxSuc IxZero
add1Ix (SSuc n@(SSuc _)) IxZero = IxSuc IxZero
add1Ix (SSuc n@(SSuc _)) (IxSuc i) = IxSuc (add1Ix n i)

-- {-@ reflect sub1Ix @-}
sub1Ix :: SNat n -> Ix n -> Ix n
sub1Ix SZero i = i
sub1Ix (SSuc n) IxZero = IxZero
sub1Ix (SSuc n) (IxSuc i) = undefined

-- sub1Ix SZero i = i
-- sub1Ix (SSuc n) IxZero = IxZero
-- sub1Ix (SSuc n) (IxSuc IxZero) = IxZero
-- sub1Ix (SSuc n) (IxSuc (IxSuc i)) = undefined

-- |
-- = Vector
data Vec :: Nat -> * -> * where
  Nil :: Vec Zero e
  Cons :: e -> Vec n e -> Vec (Suc n) e

instance Eq e => Eq (Vec n e) where
  Nil == Nil = True
  Cons x xs == Cons y ys = x == y && xs == ys

{-@
type PermutationVec e V1 V2 = Eq e => Equal (e -> Int) {countVec V1} {countVec V2}
@-}
type PermutationVec e = Eq e => Equal (e -> Int)

countVec :: Eq e => Vec n e -> e -> Int
countVec v e = foldVec (countVec_aux e) 0 v

countVec_aux :: Eq e => e -> e -> Int -> Int
countVec_aux e e' c = if e == e' then c + 1 else c

foldVec :: (e -> a -> a) -> a -> Vec n e -> a
foldVec f a Nil = a
foldVec f a (Cons x xs) = foldVec f (f x a) xs

-- |
-- = Array

-- Array

-- {-@
-- class Array arr where
--   runArray   :: Vec n e -> arr n e a -> (Vec n e, a)
--   pureArray  :: a -> arr n e a
--   bindArray  :: arr n e a -> (a -> arr n e b) -> arr n e b
--   readArray  :: Ix n -> arr n e e
--   writeArray :: e -> Ix n -> arr n e Unit
-- @-}
class Array (arr :: Nat -> * -> * -> *) where
  runArray :: forall n e a. arr n e a -> Vec n e -> (Vec n e, a)
  pureArray :: forall n e a. a -> arr n e a
  bindArray :: forall n e a b. arr n e a -> (a -> arr n e b) -> arr n e b
  readArray :: forall n e. Ix n -> arr n e e
  writeArray :: forall n e. Ix n -> e -> arr n e Unit

{-@
type EqualArray n e a A1 A2 = Equal (Vec n e -> (Vec n e, a)) {runArray A1} {runArray A2}
@-}
type EqualArray n e a = Equal (Vec n e -> (Vec n e, a))

-- {-@ reflect execArray @-}
execArray :: Array arr => Vec n e -> arr n e a -> Vec n e
execArray v a = let (v', _) = runArray a v in v'

-- {-@ reflect seqArray @-}
seqArray :: Array arr => arr n e a -> arr n e b -> arr n e b
seqArray a1 a2 = bindArray a1 (constant a2)

-- swap

-- {-@ reflect swap @-}
swap :: Array arr => Ix n -> Ix n -> arr n e Unit
swap i j = bindArray (readArray i) (swap_aux1 i j)

-- {-@ reflect swap_aux1 @-}
swap_aux1 :: Array arr => Ix n -> Ix n -> e -> arr n e Unit
swap_aux1 i j x = bindArray (readArray j) (swap_aux2 i j x)

-- {-@ reflect swap_aux2 @-}
swap_aux2 :: Array arr => Ix n -> Ix n -> e -> e -> arr n e Unit
swap_aux2 i j x y = seqArray (writeArray j x) (writeArray i y)

-- |
-- == Array Permutation

-- | An array operation is a _permutation_ if it preserves the counts of elements (up to `Eq`).

{-@
type Permutation arr n e A = Eq e => Equal (Vec n e -> e -> Int) {permutation_aux a v e} {countVec}
@-}
type Permutation arr n e = Eq e => Equal (Vec n e -> e -> Int)

-- {-@ reflect permutation_aux @-}
permutation_aux :: (Array arr, Eq e) => arr n e a -> Vec n e -> e -> Int
permutation_aux a v e = countVec (execArray v a) e

-- |
-- == Array Sorting

{-@
type Sorted arr n e A = Equal (Ix n -> Ix n -> arr n e Bool) {sorted_aux A} {constant2 A}
@-}
type Sorted arr n e = Equal (Ix n -> Ix n -> arr n e Bool)

-- {-@ reflect sorted_aux @-}
sorted_aux :: (Array arr, Ord e) => arr n e a -> Ix n -> Ix n -> arr n e Bool
sorted_aux a i j = seqArray a (sortedAt i j)

-- {-@ reflect sortedAt @-}
sortedAt :: (Array arr, Ord e) => Ix n -> Ix n -> arr n e Bool
sortedAt i j =
  if leIx i j
    then bindArray (readArray i) (sortedAt_aux1 j)
    else pureArray True

-- {-@ reflect sortedAt_aux1 @-}
sortedAt_aux1 :: (Array arr, Ord e) => Ix n -> e -> arr n e Bool
sortedAt_aux1 j e1 = bindArray (readArray j) (sortedAt_aux2 e1)

-- {-@ reflect sortedAt_aux2 @-}
sortedAt_aux2 :: (Array arr, Ord e) => e -> e -> arr n e Bool
sortedAt_aux2 e1 e2 = pureArray (e1 <= e2)

-- |
-- == Quicksort

{-@ lazy quickpartition @-}
{-@
quickpartition ::
  (Array arr, Ord e) =>
  len:SNat n ->
  iLf:Ix n ->
  iLo:{iLo:Ix n | leIx iLf iLo} ->
  iHi:{iHi:Ix n | leIx iLf iHi && leIx iHi iLo} ->
  iP:{iP:Ix n | leIx iLo iP} ->
  arr n e ({iP':Ix n | leIx iLf iP' && leIx iP' iP})
@-}
quickpartition :: (Array arr, Ord e) => SNat n -> Ix n -> Ix n -> Ix n -> Ix n -> arr n e (Ix n)
quickpartition len iLf iLo iHi iP =
  if ltIx iLo iP
    then bindArray (readArray iLo) (quickpartition_aux1 len iLf iLo iHi iP)
    else
      seqArray
        (swap iHi iP)
        (pureArray (iHi `by` undefined `by` assume (leIx iLf iHi)))

{-@ lazy quickpartition_aux1 @-}
{-@
quickpartition_aux1 ::
  (Array arr, Ord e) =>
  len:SNat n ->
  iLf:Ix n ->
  iLo:{iLo:Ix n | leIx iLf iLo} ->
  iHi:{iHi:Ix n | leIx iLf iHi && leIx iHi iLo} ->
  iP:{iP:Ix n | ltIx iLo iP} ->
  e ->
  arr n e ({iP':Ix n | leIx iLf iP' && leIx iP' iP})
@-}
quickpartition_aux1 :: (Array arr, Ord e) => SNat n -> Ix n -> Ix n -> Ix n -> Ix n -> e -> arr n e (Ix n)
quickpartition_aux1 len iLf iLo iHi iP lo =
  bindArray (readArray iP) (quickpartition_aux2 len iLf iLo iHi iP lo)

{-@ lazy quickpartition_aux2 @-}
{-@
quickpartition_aux2 ::
  (Array arr, Ord e) =>
  len:SNat n ->
  iLf:Ix n ->
  iLo:{iLo:Ix n | leIx iLf iLo} ->
  iHi:{iHi:Ix n | leIx iLf iHi && leIx iHi iLo} ->
  iP:{iP:Ix n | ltIx iLo iP} ->
  e ->
  e ->
  arr n e ({iP':Ix n | leIx iLf iP' && leIx iP' iP})
@-}
quickpartition_aux2 :: (Array arr, Ord e) => SNat n -> Ix n -> Ix n -> Ix n -> Ix n -> e -> e -> arr n e (Ix n)
quickpartition_aux2 len iLf iLo iHi iP lo p =
  if lo > p
    then
      let iLo' = add1Ix len iLo
       in quickpartition
            len
            iLf
            (iLo' `by` leIx_trans iLf iLo iLo' trivial (leIx_add1Ix len iLo))
            (iHi `by` leIx_trans iHi iLo iLo' trivial (leIx_add1Ix len iLo))
            (iP `by` ltIx_imp_leIx_add1Ix len iLo iP)
    else
      let iLo' = add1Ix len iLo
          iHi' = add1Ix len iHi
       in seqArray
            (swap iLo iHi)
            ( quickpartition
                len
                iLf
                (iLo' `by` leIx_trans iLf iLo iLo' trivial (leIx_add1Ix len iLo))
                ( iHi'
                    `by` leIx_trans iLf iHi iHi' trivial (leIx_add1Ix len iHi)
                    `by` leIx_add1Ix_add1Ix len iHi iLo
                )
                (iP `by` ltIx_imp_leIx_add1Ix len iLo iP)
            )

-- {-@ lazy quicksort_aux1 @-}
{-@
quicksort_aux1 ::
  (Array arr, Ord e) =>
  len:SNat n ->
  i:Ix n ->
  j:Ix n ->
  arr n e Unit
@-}
quicksort_aux1 :: (Array arr, Ord e) => SNat n -> Ix n -> Ix n -> arr n e Unit
quicksort_aux1 len i j =
  if ltIx i j
    then
      bindArray
        ( quickpartition
            len
            i
            (i `by` leIx_refl i)
            (i `by` leIx_refl i)
            (j `by` ltIx_imp_leIx i j)
        )
        (quicksort_aux2 len i j)
    else pureArray unit

-- {-@ lazy quicksort_aux2 @-}
{-@
quicksort_aux2 ::
  (Array arr, Ord e) =>
  len:SNat n ->
  i:Ix n ->
  j:{j:Ix n | ltIx i j} ->
  iP:Ix n ->
  arr n e Unit
@-}
quicksort_aux2 :: (Array arr, Ord e) => SNat n -> Ix n -> Ix n -> Ix n -> arr n e Unit
quicksort_aux2 len i j IxZero = undefined
quicksort_aux2 len i j iP@(IxSuc _) =
  seqArray
    ( if leIx i (sub1Ix len iP) && ltIx (sub1Ix len iP) j && iP /= IxZero
        then quicksort_aux1 len i (sub1Ix len iP)
        else pureArray unit
    )
    ( if leIx (add1Ix len iP) j && ltIx i iP && iP /= maxIx len
        then quicksort_aux1 len (add1Ix len iP) j
        else pureArray unit
    )

{-@
ltIx_imp_leIx_add1Ix :: n:SNat n -> i:Ix n -> {j:Ix n | ltIx i j} -> {leIx (add1Ix n i) j}
@-}
ltIx_imp_leIx_add1Ix :: SNat n -> Ix n -> Ix n -> Proof
ltIx_imp_leIx_add1Ix n i j = undefined

{-@
ltIx_imp_leIx :: i:Ix n -> j:{Ix n | ltIx i j} -> {leIx i j}
@-}
ltIx_imp_leIx :: Ix n -> Ix n -> Proof
ltIx_imp_leIx i j = undefined

{-@
leIx_add1Ix :: n:SNat n -> i:Ix n -> {leIx i (add1Ix n i)}
@-}
leIx_add1Ix :: SNat n -> Ix n -> Proof
leIx_add1Ix n i = undefined

{-@
leIx_add1Ix_add1Ix :: n:SNat n -> i:Ix n -> {j:Ix n | leIx i j} -> {leIx (add1Ix n i) (add1Ix n j)}
@-}
leIx_add1Ix_add1Ix :: SNat n -> Ix n -> Ix n -> Proof
leIx_add1Ix_add1Ix n i j = undefined

{-@
leIx_trans :: i:Ix n -> j:Ix n -> k:Ix n -> {_:Proof | leIx i j} -> {_:Proof | leIx j k} -> {leIx i k}
@-}
leIx_trans :: Ix n -> Ix n -> Ix n -> Proof -> Proof -> Proof
leIx_trans i j k leIx_i_j leIx_j_k = undefined

{-@ automatic-instances leIx_refl @-}
{-@
leIx_refl :: i:Ix n -> {leIx i i}
@-}
leIx_refl :: Ix n -> Proof
leIx_refl IxZero = trivial
leIx_refl (IxSuc i) = leIx_refl i
