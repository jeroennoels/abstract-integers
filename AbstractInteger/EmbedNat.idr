module AbstractInteger.EmbedNat

import Util.Common
import AbstractInteger.Interfaces
--import AbstractInteger.Additive
--import AbstractInteger.OrderedAdditive

%access export
%default total

orderPlusOne : IntegerDomain s loe => (a : s) -> loe a (One |+| a) 
orderPlusOne {loe} a = qed where

   o1 : loe Zero One
   o1 = onePositive {lessOrEq = loe}
   
   o2 : Zero |+| a `loe` One |+| a
   o2 = translateOrderR {rel = loe} Zero One a o1
                  
   qed = rewriteRelation loe (plusNeutralL a) Refl o2


zeroLessThanNat : IntegerDomain s loe => loe (nat 0) (nat n)
zeroLessThanNat {loe} {n = Z} = reflexive {po = loe} (nat 0)
zeroLessThanNat {s} {loe} {n = S k} = let
    hyp = zeroLessThanNat {loe} {n = k} 
    lll = orderPlusOne {loe} (nat {s} k) 
    bbb = transitive {po = loe} _ _ _ hyp lll
    aaa = embedNatS {s} {lessOrEq = loe} {n = k}
    in rewriteRelation loe Refl (sym aaa) bbb


-- orderSucc : IntegerDomain s loe => LTE n m -> loe (nat n) (nat m)
-- orderSucc LTEZero = ?orderSucc_rhs_1
-- orderSucc LTESucc x = ?orderSucc_rhs_2



