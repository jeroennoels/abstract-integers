module AbstractInteger.EmbedNat

import Util.Common
import AbstractInteger.Interfaces
import AbstractInteger.Additive

%default total

export
orderPlusOne : IntegerDomain s loe => .(a : s) -> loe a (One |+| a)
orderPlusOne {loe} a = qed where

   o1 : loe Zero One
   o1 = onePositive {lessOrEq = loe}

   o2 : Zero |+| a `loe` One |+| a
   o2 = translateOrderR {rel = loe} Zero One a o1

   qed = rewriteRelation loe (plusNeutralL a) Refl o2


export
zeroLessThanNat : IntegerDomain s loe => loe (nat 0) (nat n)
zeroLessThanNat {loe} {n = Z} = reflexive {po = loe} (nat 0)
zeroLessThanNat {s} {loe} {n = S k} =
    rewriteRelation loe Refl (sym o3) o2 where

    ih : nat 0 `loe` nat k
    ih = zeroLessThanNat {loe} {n = k}

    o1 : nat k `loe` One |+| nat k
    o1 = orderPlusOne {loe} (nat {s} k)

    o2 : nat 0 `loe` One |+| nat k
    o2 = transitive {po = loe} _ _ _ ih o1

    o3 : nat {s} (S k) = One |+| nat k
    o3 = embedNatS {s}


export
orderSucc : IntegerDomain s loe => .LTE n m -> loe (nat n) (nat m)
orderSucc {loe} LTEZero = zeroLessThanNat {loe}
orderSucc {loe} {s} {n = S k} {m = S j} (LTESucc prf) =
    rewriteRelation loe (sym embedNatS) (sym embedNatS) o1 where

    ih : loe (nat k) (nat j)
    ih = orderSucc {loe} prf

    o1 : One |+| nat k `loe` One |+| nat j
    o1 = translateOrderL {rel = loe} _ _ One ih


export
natInterval : IntegerDomain s loe => (x : Nat) -> .{a,b : Nat} -> 
    .{auto p : LTE a x} -> .{auto q : LTE x b} -> Interval loe (nat a) (nat b)
natInterval {loe} x {p} {q} = 
    Between (nat x) (orderSucc {loe} p) (orderSucc {loe} q)


export
plusNatZ : IntegerDomain s loe => (a : s) -> a |+| nat 0 = a
plusNatZ a = o1 `trans` plusNeutralR a
  where
    o1 : a |+| nat 0 = a |+| Zero
    o1 = cong {f = translateL a} embedNatZ
