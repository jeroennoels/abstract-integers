module AbstractInteger.Theory

import public Util.Common
import public AbstractInteger.Interfaces
import Util.LocalContrib
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


exclusiveOrder : IntegerDomain s loe => (a,b : s) ->
    EitherErased (a |+| One  `loe` b) (b `loe` a)
exclusiveOrder {loe} a b =
  case order {to = loe} a b of
    Left ab => case decEq a b of
        Yes Refl => RightErased (reflexive a)
        No contra => LeftErased (plusOneLessOrEq ab contra)
    Right ba => RightErased ba


splitInterval : IntegerDomain s loe => (a,b,c : s) ->
    (x : Interval loe a b) ->
    Either (Interval loe a c) (Interval loe (c |+| One) b)
splitInterval {loe} a b c (Between x xlo xhi) = 
  case exclusiveOrder {loe} c x of
    LeftErased prf => Right (Between x prf xhi)
    RightErased prf => Left (Between x xlo prf)
    

-- data Carry = M | O | P
-- carry : PartiallyOrderedAdditiveGroup s rel => .{u,v : s} ->
--     SymRange rel (u |+| v) -> (Carry, SymRange rel u)


