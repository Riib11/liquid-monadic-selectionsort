{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--typeclass" @-}
{-@ LIQUID "--ple-local" @-}

module QuickSort.ArrayProto where

import Relation.Equality.Leibniz
import Refined.Data.Unit
import Proof
import QuickSort.Array

{-@
pf :: {1 == 1}
@-}
pf :: Proof 
pf = trivial