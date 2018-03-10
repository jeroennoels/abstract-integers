module AbstractInteger.Interfaces

import public Util.Common
import public Util.Law
import public Decidable.Order

%default total

infixl 8 |+|

public export
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


public export
interface (AdditiveGroup s, Poset s rel) =>
    PartiallyOrderedAdditiveGroup s (rel : Rel s)
  where
    translateOrderL : isTranslationInvariantL (|+|) rel
    translateOrderR : isTranslationInvariantR (|+|) rel    
    maybeOrdered : (a,b : s) -> Maybe (rel a b) 
