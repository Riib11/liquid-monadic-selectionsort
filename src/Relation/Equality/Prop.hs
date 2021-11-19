module Relation.Equality.Prop where

{-@
data EqualProp a = EqualProp
@-}
data EqualProp a = EqualProp

{-@
measure eqp :: a -> a -> Bool
@-}

{-@
type EqP a X Y = {w:EqualProp a | eqp X Y}
@-}
