module Refined.Data.UniqueList where

import Prelude hiding (length, minimum, min, delete)
import Language.Haskell.Liquid.ProofCombinators

{-@
data UniqueList where
    Nil :: UniqueList
  | Cons :: x:Int -> {xs:UniqueList | not (contains x xs)} -> UniqueList
@-}
data UniqueList = Nil | Cons Int (UniqueList)
  deriving (Show)

infixr 5 `Cons`

{-@ reflect contains @-}
contains :: UniqueList -> Int -> Bool
contains Nil y = False 
contains (Cons x xs) y = if x == y then True else contains xs y

