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

export
commuteAdditiveGroupOrderL : AdditiveGroup s => (rel : Rel s) -> 
   Law.translationInvariantOrderL Interfaces.add rel ->
   Law.translationInvariantOrderR Interfaces.add rel
commuteAdditiveGroupOrderL rel left = 
   Law.commuteTranslationInvariantOrderL Interfaces.add rel plusCommutative left


public export
interface (AdditiveGroup s, Poset s rel) =>
    PartiallyOrderdAdditiveGroup s (rel : s -> s -> Type)
where
    translationInvariantOrderL : Law.translationInvariantOrderL Interfaces.add rel
    translationInvariantOrderR : Law.translationInvariantOrderR Interfaces.add rel

