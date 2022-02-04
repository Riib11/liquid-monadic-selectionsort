{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module QuickSort.Correctness where

import Proof
import QuickSort.Array
import QuickSort.Implementation
import Refined.Data.Int
import Refined.Data.Unit
import Refined.Function
import Relation.Equality.Leibniz
