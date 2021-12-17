{-# LANGUAGE GADTs, DataKinds, TypeOperators, TypeFamilies, ExplicitForAll, ScopedTypeVariables #-}
{-@ LIQUID "--no-totality" @-}

module QuickSort.MonadicV5 where

import Proof
-- import Relation.Equality.Prop
import Relation.Equality.Leibniz
import Refined.Function
import Refined.Data.Unit
import Refined.Data.Int

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

data SNat :: Nat -> * where
  SZero :: SNat Zero
  SSuc :: SNat n -> SNat (Suc n)

-- Ix

data Ix :: Nat -> * where
  ZeroIx :: Ix (Suc n)
  SucIx :: Ix n -> Ix (Suc n)

instance Eq (Ix n) where
  ZeroIx == ZeroIx = True
  SucIx i == SucIx j = i == j

{-@ reflect leIx @-}
leIx :: Ix n -> Ix n -> Bool
leIx ZeroIx _ = True
leIx (SucIx i) ZeroIx = False
leIx (SucIx i) (SucIx j) = leIx i j

-- |
-- = Vector

data Vec :: Nat -> * -> * where
  Nil :: Vec Zero e
  Cons :: e -> Vec n e -> Vec (Suc n) e

instance Eq e => Eq (Vec n e) where
  Nil == Nil = True
  Cons x xs == Cons y ys = x == y && xs == ys

{-@
type PermutationVec e V1 V2 = Eq e => EqL (e -> Int) {countVec V1} {countVec V2}
@-}
type PermutationVec e = Eq e => EqL (e -> Int)

countVec :: Eq e => Vec n e -> e -> Int
countVec v e = foldVec (countVec_aux e) 0 v

countVec_aux :: Eq e => e -> e -> Int -> Int
countVec_aux e e' c = if e == e' then c + 1 else c

foldVec :: (e -> a -> a) -> a -> Vec n e -> a
foldVec f a Nil = a
foldVec f a (Cons x xs) = foldVec f (f x a) xs

-- |
-- = Array

-- Arr

-- {-@
-- class Arr arr where
--   runArr   :: Vec n e -> arr n e a -> (Vec n e, a)
--   pureArr  :: a -> arr n e a
--   bindArr  :: arr n e a -> (a -> arr n e b) -> arr n e b
--   readArr  :: Ix n -> arr n e e
--   writeArr :: e -> Ix n -> arr n e Unit
-- @-}
class Arr (arr :: Nat -> * -> * -> *) where
  runArr   :: forall n e a. arr n e a -> Vec n e -> (Vec n e, a)
  pureArr  :: forall n e a. a -> arr n e a
  bindArr  :: forall n e a b. arr n e a -> (a -> arr n e b) -> arr n e b
  readArr  :: forall n e. Ix n -> arr n e e
  writeArr :: forall n e. e -> Ix n -> arr n e Unit

{-@
type EqArr n e a A1 A2 = EqL (Vec n e -> (Vec n e, a)) {runArr A1} {runArr A2}
@-}
type EqArr n e a = EqL (Vec n e -> (Vec n e, a))

execArr :: Arr arr => Vec n e -> arr n e a -> Vec n e
execArr v a = let (v', _) = runArr a v in v'

seqArr :: Arr arr => arr n e a -> arr n e b -> arr n e b
seqArr a1 a2 = bindArr a1 (constant a2)

-- |
-- == Array Permutation

-- | An array operation is a _permutation_ if it preserves the counts of elements (up to `Eq`).

{-@
type PermutationArr arr n e A = Eq e => EqL (Vec n e -> e -> Int) {permutation_aux a v e} {countVec}
@-}
type PermutationArr arr n e = Eq e => EqL (Vec n e -> e -> Int)

permutation_aux :: (Arr arr, Eq e) => arr n e a -> Vec n e -> e -> Int
permutation_aux a v e = countVec (execArr v a) e

-- |
-- == Array Sorting

{-@
type SortedArr arr n e A = EqL (Ix n -> Ix n -> arr n e Bool) {sorted_aux A} {constant2 A}
@-}
type SortedArr arr n e = EqL (Ix n -> Ix n -> arr n e Bool)

-- TODO: reflect `sortedAt` and `seqArr`
sorted_aux :: (Arr arr, Ord e) => arr n e a -> Ix n -> Ix n -> arr n e Bool
sorted_aux a i j = seqArr a (sortedAt i j)

-- TODO: reflect `pureArr`
-- {-@ reflect sortedAt @-}
sortedAt :: (Arr arr, Ord e) => Ix n -> Ix n -> arr n e Bool
sortedAt i j = if leIx i j
  then bindArr (readArr i) (sortedAt_aux1 j)
  else pureArr True

sortedAt_aux1 :: (Arr arr, Ord e) => Ix n -> e -> arr n e Bool
sortedAt_aux1 j e1 = bindArr (readArr j) (sortedAt_aux2 e1)

sortedAt_aux2 :: (Arr arr, Ord e) => e -> e -> arr n e Bool
sortedAt_aux2 e1 e2 = pureArr (e1 <= e2)