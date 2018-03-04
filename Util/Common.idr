module Util.Common

%default total
%access public export

Rel : Type -> Type
Rel s = s -> s -> Type

Binop : Type -> Type
Binop s = s -> s -> s

-- data Interval : Rel s -> s -> s -> Type where
-- Between : (x : s) -> .(a, b : s) -> .rel a x -> .rel x b -> Interval rel a b
