module AbstractInteger.Interfaces

import public Util.Common
import public Util.Law
import public Decidable.Order

%access public export
%default total

infixl 8 |+|


interface AdditiveGroup s where
    (|+|) : Binop s
    Zero : s
    neg : s -> s
    plusAssoc : isAssociative (|+|)
    plusCommutes : isCommutative (|+|)
    plusNeutralL : isNeutralL (|+|) Zero
    plusNeutralR : isNeutralR (|+|) Zero
    plusInverseL : isInverseL (|+|) Zero neg
    plusInverseR : isInverseR (|+|) Zero neg

    plusNeutralR = commuteNeutralL (|+|) Zero plusCommutes plusNeutralL
    plusInverseR = commuteInverseL (|+|) Zero neg plusCommutes plusInverseL


interface (AdditiveGroup s, Poset s rel) =>
    PartiallyOrderedAdditiveGroup s (rel : Rel s)
  where
    translateOrderL : isTranslationInvariantL (|+|) rel
    translateOrderR : isTranslationInvariantR (|+|) rel


interface (DecEq s,
           Ordered s lessOrEq,
           PartiallyOrderedAdditiveGroup s lessOrEq) =>
    IntegerDomain s (lessOrEq : Rel s) | s
  where
    One : s
    nat : Nat -> s
    embedNatZ : nat Z = Zero
    embedNatS : nat (S n) = One |+| nat n
    plusOneLessOrEq : a `lessOrEq` b -> Not (a = b) -> a |+| One `lessOrEq` b
    onePositive : Zero `lessOrEq` One
