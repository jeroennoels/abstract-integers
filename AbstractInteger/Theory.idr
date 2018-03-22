module AbstractInteger.Theory

import public Util.Common
import public AbstractInteger.Interfaces
import Util.LocalContrib
import AbstractInteger.Additive
import AbstractInteger.Lemma

%access export
%default total


shiftInterval : PartiallyOrderedAdditiveGroup s rel => (c : s) ->
    Interval rel a b -> Interval rel (a |+| c) (b |+| c)
shiftInterval {a} {b} c (Between x ax xb) =
    Between (x |+| c) (translateOrderR a x c ax) (translateOrderR x b c xb)


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


semiRangeToSymRange : PartiallyOrderedAdditiveGroup s rel => 
    rel Zero b -> rel b a -> Interval rel (neg a) b -> SymRange rel a
semiRangeToSymRange {rel} {a} {b} pos ba (Between x pp qq) = 
    Between x pp (transitive x b a qq ba)

public export
data Carry = M | O | P

sign : UnitalRing s => Carry -> s
sign M = neg One
sign O = Zero
sign P = One


orderPlusOne : IntegerDomain s loe => (a : s) -> loe a (a |+| One) 
orderPlusOne {loe} a = 
   let lala = translateOrderL {rel = loe} Zero One a 
                  (onePositive {lessOrEq = loe}) 
       bbb =  plusNeutralR a
   in rewriteRelation loe bbb Refl lala

zeroLessThanOne : IntegerDomain s loe => loe Zero One
zeroLessThanOne {s} {loe} = let lala = orderPlusOne {loe} Zero 
                                brol = plusNeutralL {s} One 
                            in rewrite sym brol in lala 

oneLessThanTwo : IntegerDomain s loe => loe One (One |+| One)
oneLessThanTwo {loe} = orderPlusOne {loe} One

zeroLessThanTwo : IntegerDomain s loe => loe Zero (One |+| One)
zeroLessThanTwo {loe} = transitive {po = loe} _ _ _ (zeroLessThanOne {loe}) 
                            (oneLessThanTwo {loe})

onePlusCarry : IntegerDomain s loe => Carry -> Interval loe Zero (One |+| One)
onePlusCarry {loe} M = Between Zero (reflexive {po = loe} Zero) 
                           (zeroLessThanTwo {loe})   
onePlusCarry {loe} O = Between One (zeroLessThanOne {loe}) (oneLessThanTwo {loe})
onePlusCarry {loe} P = Between (One |+| One) (zeroLessThanTwo {loe})
                           (reflexive {po = loe} _)


rewriteInterval : PartiallyOrderedAdditiveGroup s rel =>
    Interval rel (neg (u |+| u) |+| u |+| Zero) (neg u |+| u |+| a) ->
    Interval rel (neg u) a
rewriteInterval {u} {a} (Between x lo hi) = 
    Between x 
      (rewrite sym (plusNeutralR (neg u)) in 
       rewrite sym (negatePlusPlus u u) in lo)
      (rewrite sym (plusInversePlusL a u) in hi)



carry : IntegerDomain s loe => (u : s) -> loe (One |+| One) u -> 
    SymRange loe (u |+| u) -> Carry -> SymRange loe u
carry {s} {loe} u moreThanTwo x c = 
  let cPlus1 = onePlusCarry {loe} c 
      a = fromInterval cPlus1 in
  case splitIntervalL (neg u) x of
    Left x1 => let shift = shiftInterval u x1 
                   brol = plusOnIntervals shift cPlus1
                   semi = rewriteInterval brol in
                   semiRangeToSymRange (zeroLessThanTwo {loe}) moreThanTwo semi
    Right x1 => 
      case splitIntervalR u x1 of
        Left (Between x2 pp qq) => ?ooo-- Between x2 pp qq
        Right x2 => ?mmm
        
