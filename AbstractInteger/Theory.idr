module AbstractInteger.Theory

import public Util.Common
import public AbstractInteger.Interfaces
import AbstractInteger.Additive
import public AbstractInteger.OrderedAdditive
import public AbstractInteger.Interval

%access export
%default total


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


-- redo all of the following using an embedding of Nat

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
        
