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


||| multiplicative structure to be added later
interface AdditiveGroup s => UnitalRing s where
    One : s


interface (UnitalRing s,
           DecEq s,
           Ordered s lessOrEq,
           PartiallyOrderedAdditiveGroup s lessOrEq) =>
    IntegerDomain s (lessOrEq : Rel s)
  where
    plusOneLessOrEq : a `lessOrEq` b -> Not (a = b) -> a |+| One `lessOrEq` b
