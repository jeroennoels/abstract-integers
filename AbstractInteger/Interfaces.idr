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
    plusAssociative : isAssociative (|+|)
    plusCommutative : isCommutative (|+|)
    plusNeutralL : isNeutralL (|+|) zero
    plusNeutralR : isNeutralR (|+|) zero
    plusInverseL : isInverseL (|+|) zero neg
    plusInverseR : isInverseR (|+|) zero neg

    plusNeutralR = commuteNeutralL (|+|) zero plusCommutative plusNeutralL
    plusInverseR = commuteInverseL (|+|) zero neg plusCommutative plusInverseL


export
commuteAdditiveGroupOrderL : AdditiveGroup s => (rel : Rel s) ->
    isTranslationInvariantL (|+|) rel ->
    isTranslationInvariantR (|+|) rel
commuteAdditiveGroupOrderL rel left =
    commuteTranslationInvariantL (|+|) rel plusCommutative left


public export
interface (AdditiveGroup s, Poset s rel) =>
    PartiallyOrderedAdditiveGroup s (rel : Rel s)
  where
    translateOrderL : isTranslationInvariantL {s} (|+|) rel
    translateOrderR : isTranslationInvariantR {s} (|+|) rel
