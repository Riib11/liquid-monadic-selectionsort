-- {-@ LIQUID "--compile-spec" @-}
module Refined.Data.ListProto where

import Bot
import Proof
import Refined.Data.List
import Prelude hiding (all, any, length, min, minimum)

-- select_leAll

{-@ automatic-instances select_leAll @-}
{-@
select_leAll ::
  {xs:List | 0 < length xs} ->
  LeAll {hd (select xs)} {tl (select xs)}
@-}
select_leAll :: List -> LeAll
select_leAll (Cons x Nil) y = trivial
{-
G: contains (tl (select xs)) y => y <= hd (select xs)

if H1: x1 <= x2 then
  let Cons x' xs' = select (Cons x1 xs) in
  G: contains (Cons x2 xs') y => x' <= y
  if H2: contains (Cons x2 xs') y then
    G: x' <= y
    H2: \z -> contains xs' z => x' <= z // select_leAll (Cons x1 xs)
    H3: y == x2 || contains xs' y // contains_cons (Cons x2 xs') y
    if H4: y == x2 then
        p: Permuted {Cons x1 xs} {Cons x' xs'} := permuted_select (Cons x1 xs)
        H5: x1 == x' || contains xs' x1 //
          contains_cons
          (Cons x' xs')
            (x1 `by` contains_permuted (Cons x1 xs) (Cons x' xs') p (x1 `by_refinement` hd (Cons x1 xs)))
        if H6: x1 == x' then
          H7: x' <= x1 // H6
          H8: x' <= x2 // H1, H7
          G:  x' <= y  // H4, H8
        else H6: contains xs' x1
          H7: x' <= x1 // H2 x1 i.e. select_leAll (Cons x1 xs) x1
          H8: x' <= x2 // H1, H7
          G:  x' <= y  // H4, H8
    else H4: contains xs' y
      G: x' <= y // H2 y i.e. select_leAll (Cons x1 xs) y
  else H2: not (contains (Cons x2 xs') y)
    G: True // trivial
else H1: x2 < x1
  let Cons x' xs' = select (Cons x2 xs) in
  G: x' <= y
  if H2: contains (Cons x1 xs') y then
      G: x' <= y
      H2: \z -> contains xs' z => x' <= z // select_leAll (Cons x2 xs)
      H3: y == x1 || contains xs' y // contains_cons (Cons x1 xs') y
      if H4: y == x1 then
        p: Permuted {Cons x2 xs} {Cons x' xs'} := permuted_select (Cons x2 xs)
        H5: x1 == x' || contains xs' x2 //
          contains_cons
          (Cons x' xs')
            (x2 `by` contains_permuted (Cons x2 xs) (Cons x' xs') p
                      (x2 `by_refinement` hd (Cons x2 xs)))
        if H6: x2 == x' then
          H7: x' <= x2 // H6
          H8: x' <= x1 // H1, H7
          G:  x' <= y  // H4, H8
        else H6: contains xs' x2
          H7: x' <= x2 // H2 x1 i.e. select_leAll (Cons x2 xs)
          H8: x' <= x1 // H1, H7
          G:  x' <= y  // H4, H8
      else H4: contains xs' y
        G: x' <= y // H2 y i.e. select_leAll (Cons x2 xs)
    else H2: not (contains (Cons x2 xs') y)
      G: True // trivial
-}
select_leAll (Cons x1 (Cons x2 xs)) y =
  if x1 <= x2 -- H1
    then
      let Cons x' xs' = select (Cons x1 xs)
       in if contains (Cons x2 xs') y
            then -- H2

              if y == x2
                then -- H4

                  if x1 == x'
                    then -- H6

                      trivial
                        -- `by` assume (contains (Cons x' xs') x1)
                        `by` contains_hd (Cons x' xs')
                        `by` contains_hd (Cons x2 xs')
                        `by` assume (contains (Cons x' xs') x')
                        `by` contains_eq (Cons x' xs') x' x1
                        `by` select_leAll (Cons x1 xs) x1
                        `by` assume (contains (Cons x' xs') x1)
                        `by` contains_permuted
                          (Cons x1 xs)
                          (Cons x' xs')
                          (permuted_select (Cons x1 xs))
                          {-
                          The inferred type
                            VV : {v : GHC.Types.Int | v == x}
                          .
                          is not a subtype of the required type
                            VV : {VV : GHC.Types.Int | contains (Cons x xs) VV}
                          .
                          in the context
                            xs : {v : Refined.Data.List.List | 0 <= length v}

                            x : GHC.Types.Int
                          -}
                          x1
                    else -- H6

                      trivial
                        `by` assume (contains (Cons x1 xs) x1)
                        `by` assume (contains (Cons x' xs') x1)
                        `by` contains_hd (Cons x2 xs')
                        `by` contains_tl (Cons x' xs') x1
                        `by` select_leAll (Cons x1 xs) x1
                        `by` contains_permuted
                          (Cons x1 xs)
                          (Cons x' xs')
                          (permuted_select (Cons x1 xs))
                          x1
                else -- H4
                  select_leAll (Cons x1 xs) y
            else -- H2
              trivial
    else -- H1
      undefined

-- let Cons x' xs' = select (Cons x2 xs)
--  in if contains (Cons x1 xs') y
--       then -- H2

--         if y == x1
--           then -- H4

--             if x2 == x'
--               then -- H6

--                 trivial
--                   `by` assume (contains (Cons x2 xs) x2)
--                   `by` contains_hd (Cons x1 xs')
--                   `by` contains_hd (Cons x' xs')
--                   `by` contains_hd (Cons x2 xs)
--                   `by` select_leAll (Cons x2 xs) x2
--                   `by` contains_permuted
--                     (Cons x2 xs)
--                     (Cons x' xs')
--                     (permuted_select (Cons x2 xs))
--                     x2
--               else -- H6

--                 trivial
--                   `by` assume (contains (Cons x' xs') x2)
--                   `by` assume (x2 /= hd (Cons x' xs'))
--                   `by` contains_hd (Cons x2 xs)
--                   `by` contains_hd (Cons x1 xs')
--                   `by` contains_tl (Cons x' xs') x2
--                   `by` select_leAll (Cons x2 xs) x2
--                   `by` contains_permuted
--                     (Cons x2 xs)
--                     (Cons x' xs')
--                     (permuted_select (Cons x2 xs))
--                     x2
--           else -- H4
--             select_leAll (Cons x2 xs) y
--       else -- H2
--         trivial
