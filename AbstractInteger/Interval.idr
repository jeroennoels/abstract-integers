module AbstractInteger.Interval

import Util.Common
import Util.LocalContrib
import AbstractInteger.Interfaces
import AbstractInteger.Additive
import AbstractInteger.OrderedAdditive

%default total


export
shiftInterval : PartiallyOrderedAdditiveGroup s rel => (c : s) ->
    Interval rel a b -> Interval rel (a |+| c) (b |+| c)
shiftInterval {a} {b} c (Between x ax xb) =
    Between (x |+| c)
        (translateOrderR a x c ax)
        (translateOrderR x b c xb)


export
plusOnIntervals : PartiallyOrderedAdditiveGroup s rel =>
    Interval rel a b -> Interval rel c d ->
    Interval rel (a |+| c) (b |+| d)
plusOnIntervals (Between x ax xb) (Between y cy yd) =
    Between (x |+| y)
        (plusPreservesOrder _ x _ y ax cy)
        (plusPreservesOrder x _ y _ xb yd)


||| Intervals that are symmetric around Zero.
public export
SymRange : AdditiveGroup s => .(rel : Rel s) -> .(u : s) -> Type
SymRange rel u = Interval rel (neg u) u


||| Check whether @a is in the range.
export
inSymRange : PartiallyOrderedAdditiveGroup s rel =>
    (check : (a,b : s) -> Maybe (rel a b)) ->
    (a : s) -> (u : s) -> Maybe (SymRange rel u)
inSymRange check a u = let
    lower = check (neg u) a
    upper = check a u
    in liftA2 (Between a) lower upper


export
addInRange : PartiallyOrderedAdditiveGroup s rel =>
    SymRange rel u -> SymRange rel v -> SymRange rel (u |+| v)
addInRange {u} {v} =
    rewrite negatePlusAbelian u v in plusOnIntervals


||| Decide if @x is in the left interval or the right one.
||| The left one includes the pivot.
export
splitIntervalL : IntegerDomain s loe => (pivot : s) ->
    (x : Interval loe a b) ->
    Either (Interval loe a pivot)
           (Interval loe (pivot |+| One) b)
splitIntervalL {loe} pivot (Between x lo hi) =
  case exclusiveOrder {loe} pivot x of
    LeftErased prf => Right (Between x prf hi)
    RightErased prf => Left (Between x lo prf)


||| Decide if @x is in the left interval or the right one.
||| The right one includes the pivot.
export
splitIntervalR : IntegerDomain s loe => (pivot : s) ->
    (x : Interval loe a b) ->
    Either (Interval loe a (pivot |+| neg One))
           (Interval loe pivot b)
splitIntervalR pivot x =
    case splitIntervalL (pivot |+| neg One) x of
      Left aaa => Left aaa
      Right bb => let cancel = plusPlusInverseL pivot One
                  in Right (rewrite sym cancel in bb)
