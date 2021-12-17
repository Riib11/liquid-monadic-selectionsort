{-# LANGUAGE GADTs, DataKinds #-}

module Refined.Data.Vec where

import Proof

-- data Nat

{-@
data Nat = Zero | Suc Nat
@-}
data Nat = Zero | Suc Nat
  deriving (Show)

-- data Ix

data Ix :: Nat -> * where
  IxZero :: Ix (Suc n)
  IxSuc :: Ix n -> Ix (Suc n)

{-@ reflect leIx @-}
leIx :: Ix n -> Ix n -> Bool
leIx IxZero _ = True
leIx (IxSuc i) IxZero = False
leIx (IxSuc i) (IxSuc j) = leIx i j

-- type Vec

type Vec n a = Ix n -> a
