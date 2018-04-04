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
    o1 = orderPlusOne {loe} (nat k)

    o2 : nat 0 `loe` One |+| nat k
    o2 = transitive {po = loe} _ _ _ ih o1

    o3 : nat {s} (S k) = One |+| nat k
    o3 = embedNatS


export
embedNatOrder : IntegerDomain s loe => .LTE n m -> loe (nat n) (nat m)
embedNatOrder {loe} LTEZero = zeroLessThanNat {loe}
embedNatOrder {loe} {n = S k} {m = S j} (LTESucc prf) =
    rewriteRelation loe (sym embedNatS) (sym embedNatS) o1 where

    ih : loe (nat k) (nat j)
    ih = embedNatOrder {loe} prf

    o1 : One |+| nat k `loe` One |+| nat j
    o1 = translateOrderL {rel = loe} _ _ One ih


export
natInterval : IntegerDomain s loe => (x : Nat) -> .{a,b : Nat} ->
    .{auto p : LTE a x} -> .{auto q : LTE x b} -> Interval loe (nat a) (nat b)
natInterval {loe} x {p} {q} =
    Between (nat x) (embedNatOrder {loe} p) (embedNatOrder {loe} q)


export
plusNatZ : IntegerDomain s loe => (a : s) -> a |+| nat 0 = a
plusNatZ a = o1 `trans` plusNeutralR a
  where
    o1 : a |+| nat 0 = a |+| Zero
    o1 = cong {f = translateL a} embedNatZ


export
embedNatOne : IntegerDomain s loe => nat {s} 1 = One
embedNatOne = embedNatS `trans` plusNatZ One


export
embedNatAdditiveMorphism : IntegerDomain s loe => (a,b : Nat) ->
    nat a |+| nat b = nat {s} (a + b)
embedNatAdditiveMorphism Z b = plusCommutes _ _ `trans` plusNatZ (nat b)
embedNatAdditiveMorphism {s} (S a) b = rewrite o3 in o2 where

    ih : nat a |+| nat b = nat {s} (a + b)
    ih = embedNatAdditiveMorphism a b

    o1 : One |+| nat a |+| nat b = One |+| nat {s} (a + b)
    o1 = sym (plusAssoc One _ _) `trans` cong ih

    o2 : One |+| nat a |+| nat b = nat {s} (S (a + b))
    o2 = o1 `trans` sym embedNatS

    o3 : nat {s} (S a) = One |+| nat a
    o3 = embedNatS


export
embedNatTwo : IntegerDomain s loe => nat {s} 2 = double One
embedNatTwo {s} = sym o1 `trans` o2 where

    o1 : double (nat 1) = nat {s} 2
    o1 = embedNatAdditiveMorphism 1 1

    o2 : double (nat 1) = double (One {s})
    o2 = cong {f = double} embedNatOne


export
embedNatTwoMinusOne : IntegerDomain s loe => nat 2 |+| neg One = One {s}
embedNatTwoMinusOne {s} = o1 `trans` plusPlusInverseR One One
  where
    o1 : nat {s} 2 |+| neg One = double One |+| neg One
    o1 = cong {f = translateR _} embedNatTwo

