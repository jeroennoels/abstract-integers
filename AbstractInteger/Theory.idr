module AbstractInteger.Theory

import public Util.Common
import public AbstractInteger.Interfaces
import AbstractInteger.Lemma

%access export
%default total

plusPreservesOrder : PartiallyOrderedAdditiveGroup s rel => .(a,b,c,d : s) ->
    .rel a b -> .rel c d -> rel (a |+| c) (b |+| d)
plusPreservesOrder a b c d ab cd =
  let pp = translateOrderR a b c ab
      qq = translateOrderL c d b cd
  in transitive (a |+| c) _ _ pp qq


plusOnIntervals : PartiallyOrderedAdditiveGroup s rel =>
    Interval rel a b -> Interval rel c d ->
    Interval rel (a |+| c) (b |+| d)
plusOnIntervals (Between x ax xb) (Between y cy yd) = let
    pp = plusPreservesOrder _ x _ y ax cy
    qq = plusPreservesOrder x _ y _ xb yd
    in Between (x |+| y) pp qq

public export
SymRange : AdditiveGroup s => .(rel : Rel s) -> .(u : s) -> Type
SymRange rel u = Interval rel (neg u) u


inSymRange : PartiallyOrderedAdditiveGroup s rel =>
    (check : (a,b : s) -> Maybe (rel a b)) -> 
    (a : s) -> (u : s) -> Maybe (SymRange rel u)
inSymRange check a u = let
    lower = check (neg u) a
    upper = check a u
    in liftA2 (Between a) lower upper


addInRange : PartiallyOrderedAdditiveGroup s rel => .{u,v : s} ->
    SymRange rel u -> SymRange rel v -> SymRange rel (u |+| v)
addInRange {u} {v} =
    rewrite negatePlusAbelian u v in plusOnIntervals


public export
data Alt : Type -> Type -> Type where
    Aaa : a -> Alt a b
    Bbb : b -> Alt a b

exclusiveOrder : IntegerDomain s lessOrEq => (a,b : s) ->
    Alt (a |+| One  `lessOrEq` b) (b `lessOrEq` a)
exclusiveOrder {lessOrEq} a b =
  case order {to = lessOrEq} a b of
    Left ab => case decEq a b of
        Yes Refl => Bbb (reflexive {po = lessOrEq} a)
        No contra => Aaa (plusOneLessOrEq {lessOrEq} ab contra)
    Right ba => Bbb ba


-- data Carry = M | O | P
-- carry : PartiallyOrderedAdditiveGroup s rel => .{u,v : s} ->
--     SymRange rel (u |+| v) -> (Carry, SymRange rel u)


