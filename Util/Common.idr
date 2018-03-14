module Util.Common

%default total
%access public export

Rel : .Type -> Type
Rel s = s -> s -> Type

Binop : .Type -> Type
Binop s = s -> s -> s

data Interval : .Rel s -> s -> s -> Type where
    Between : .{a,b : s} ->
        (x : s) -> .rel a x -> .rel x b -> Interval rel a b

fromInterval : Interval {s} _ _ _ -> s
fromInterval (Between val _ _) = val

leftOrNothing : Either a b -> Maybe a
leftOrNothing (Left a) = Just a
leftOrNothing _ = Nothing
