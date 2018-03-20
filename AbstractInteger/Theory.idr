module AbstractInteger.Theory

import public Util.Common
import public AbstractInteger.Interfaces
import Util.LocalContrib
import AbstractInteger.Lemma

%access export
%default total


shiftInterval : PartiallyOrderedAdditiveGroup s rel => (c : s) ->
    Interval rel a b -> Interval rel (a |+| c) (b |+| c)
shiftInterval {a} {b} c (Between x ax xb) = 
    Between (x |+| c) (translateOrderR a x c ax) (translateOrderR x b c xb)


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


exclusiveOrder : IntegerDomain s loe => (a,b : s) ->
    EitherErased (a |+| One `loe` b) (b `loe` a)
exclusiveOrder {loe} a b =
  case order {to = loe} a b of
    Left ab => case decEq a b of
        Yes Refl => RightErased (reflexive a)
        No contra => LeftErased (plusOneLessOrEq ab contra)
    Right ba => RightErased ba


||| Decide if x is in the left interval or the right one.
splitIntervalL : IntegerDomain s loe => (c : s) ->
    (x : Interval loe a b) ->
    Either (Interval loe a c) (Interval loe (c |+| One) b)
splitIntervalL {loe} c (Between x xlo xhi) = 
  case exclusiveOrder {loe} c x of
    LeftErased prf => Right (Between x prf xhi)
    RightErased prf => Left (Between x xlo prf)
    
    
||| Decide if x is in the left interval or the right one.
splitIntervalR : IntegerDomain s loe => (c : s) ->
    (x : Interval loe a b) ->
    Either (Interval loe a (c |+| neg One)) (Interval loe c b)
splitIntervalR c x = 
    case splitIntervalL (c |+| neg One) x of
      Left aa => Left aa
      Right bb => let cancel = plusPlusInverseL c One in
                  Right (rewrite sym cancel in bb)

     
data Carry = M | O | P


-- carry : IntegerDomain s loe => .{u : s} ->
--     SymRange loe (u |+| u) -> (Carry, SymRange loe u)
-- carry {u} x = let
--    lala = splitIntervalL (neg u) x
--    in ?mm
