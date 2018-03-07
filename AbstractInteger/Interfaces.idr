module AbstractInteger.Interfaces

import public Util.Common
import public Util.Law
import public Decidable.Order

%default total

infixl 8 |+|

public export
interface AdditiveGroup s where
    (|+|) : Binop s
    zero : s
    neg : s -> s
    plusAssoc : isAssociative (|+|)
    plusCommutes : isCommutative (|+|)
    plusNeutralL : isNeutralL (|+|) zero
    plusNeutralR : isNeutralR (|+|) zero
    plusInverseL : isInverseL (|+|) zero neg
    plusInverseR : isInverseR (|+|) zero neg

    plusNeutralR = commuteNeutralL (|+|) zero plusCommutes plusNeutralL
    plusInverseR = commuteInverseL (|+|) zero neg plusCommutes plusInverseL


public export
interface (AdditiveGroup s, Poset s rel) =>
    PartiallyOrderedAdditiveGroup s (rel : Rel s)
  where
    translateOrderL : isTranslationInvariantL (|+|) rel
    translateOrderR : isTranslationInvariantR (|+|) rel    
    maybeOrdered : (a,b : s) -> Maybe (rel a b) 
