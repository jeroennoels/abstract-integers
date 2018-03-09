module AbstractInteger.Theory

import public Util.Common
import public AbstractInteger.Interfaces
import AbstractInteger.Lemma


%default total

export
plusPreservesOrder : PartiallyOrderedAdditiveGroup s rel => .(a,b,c,d : s) ->
    .rel a b -> .rel c d -> rel (a |+| c) (b |+| d)
plusPreservesOrder a b c d ab cd =
  let pp = translateOrderR a b c ab
      qq = translateOrderL c d b cd
  in transitive (a |+| c) _ _ pp qq

export
plusOnIntervals : PartiallyOrderedAdditiveGroup s rel =>
    Interval rel a b -> Interval rel c d ->
    Interval rel (a |+| c) (b |+| d)
plusOnIntervals (Between x ax xb) (Between y cy yd) = let
    pp = plusPreservesOrder _ x _ y ax cy
    qq = plusPreservesOrder x _ y _ xb yd
    in Between (x |+| y) pp qq

public export
SymRange : PartiallyOrderedAdditiveGroup s rel => .(u : s) -> Type
SymRange {rel} u = Interval rel (neg u) u

export
inSymRange : PartiallyOrderedAdditiveGroup s rel => (a : s) -> (u : s) ->
    Maybe (SymRange {rel} u)
inSymRange a u = let
    lower = maybeOrdered (neg u) a
    upper = maybeOrdered a u
    in liftA2 (Between a) lower upper

export
addInRange : PartiallyOrderedAdditiveGroup s rel => .{u : s} ->
    SymRange {rel} u -> SymRange {rel} u -> SymRange {rel} (u |+| u)
addInRange {u} = rewrite negatePlus u u in plusOnIntervals
