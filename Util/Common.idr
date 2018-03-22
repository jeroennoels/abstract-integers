module Util.Common

%default total
%access public export

Rel : .Type -> Type
Rel s = s -> s -> Type

Binop : .Type -> Type
Binop s = s -> s -> s

export
rewriteRelation : (rel : Rel s) -> .a = c -> .b = d -> .rel a b -> rel c d
rewriteRelation rel ac bd prf = rewrite sym ac in rewrite sym bd in prf


data Interval : .Rel s -> s -> s -> Type where
    Between : .{a,b : s} ->
        (x : s) -> .rel a x -> .rel x b -> Interval rel a b

fromInterval : Interval {s} _ _ _ -> s
fromInterval (Between val _ _) = val
