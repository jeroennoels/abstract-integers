module AbstractInteger.Interfaces

import Util.Common
import Util.Law
import Decidable.Order

%default total

public export
interface AdditiveGroup s where
    add : Binop s
    zero : s
    neg : s -> s
    plusAssociative : Law.associative add
    plusCommutative : Law.commutative add
    plusNeutralL : Law.neutralL add zero
    plusNeutralR : Law.neutralR add zero
    plusInverseL : Law.inverseL add zero neg
    plusInverseR : Law.inverseR add zero neg

    plusNeutralR = Law.commuteNeutralL add zero plusCommutative plusNeutralL
    plusInverseR = Law.commuteInverseL add zero neg plusCommutative plusInverseL


public export
interface (AdditiveGroup s, Poset s rel) =>
    PartiallyOrderdAdditiveGroup s (rel : s -> s -> Type)
  where
    translateOrderL : Law.translateOrderL Interfaces.add rel
    translateOrderR : Law.translateOrderR Interfaces.add rel


export
commuteAdditiveGroupOrderL : AdditiveGroup s => (rel : Rel s) -> 
    Law.translateOrderL Interfaces.add rel ->
    Law.translateOrderR Interfaces.add rel
commuteAdditiveGroupOrderL rel left = 
    Law.commuteTranslateOrderL Interfaces.add rel plusCommutative left
