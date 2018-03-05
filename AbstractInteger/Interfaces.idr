module AbstractInteger.Interfaces

import Util.Common
import Util.Law
import Decidable.Order

%default total

infixl 8 |+|

public export
interface AdditiveGroup s where
    (|+|) : Binop s
    zero : s
    neg : s -> s
    plusAssociative : Law.associative (|+|)
    plusCommutative : Law.commutative (|+|)
    plusNeutralL : Law.neutralL (|+|) zero
    plusNeutralR : Law.neutralR (|+|) zero
    plusInverseL : Law.inverseL (|+|) zero neg
    plusInverseR : Law.inverseR (|+|) zero neg

    plusNeutralR = Law.commuteNeutralL (|+|) zero plusCommutative plusNeutralL
    plusInverseR = Law.commuteInverseL (|+|) zero neg plusCommutative plusInverseL


public export
interface (AdditiveGroup s, Poset s rel) =>
    PartiallyOrderdAdditiveGroup s (rel : s -> s -> Type)
  where
    translateOrderL : Law.translateOrderL (|+|) rel
    translateOrderR : Law.translateOrderR (|+|) rel


export
commuteAdditiveGroupOrderL : AdditiveGroup s => (rel : Rel s) ->
    Law.translateOrderL (|+|) rel ->
    Law.translateOrderR (|+|) rel
commuteAdditiveGroupOrderL rel left =
    Law.commuteTranslateOrderL (|+|) rel plusCommutative left
