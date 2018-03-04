module PrimitiveInteger.Trusted

import Util.Law
import AbstractInteger.Interfaces
import Data.So
import Decidable.Order

%default total

primPlus : Binop Integer
primPlus = prim__addBigInt

export
data PrimitiveLTE : Integer -> Integer -> Type where
    CheckLTE : So (a <= b) -> PrimitiveLTE a b


postulate primPlusAssociative : Law.associative Trusted.primPlus
postulate primPlusCommutative : Law.commutative Trusted.primPlus
postulate primZeroL : Law.neutralL Trusted.primPlus 0
postulate primNegationL : Law.inverseL Trusted.primPlus 0 negate

public export
implementation AdditiveGroup Integer where
    add = prim__addBigInt
    zero = 0
    neg = prim__subBigInt 0
    plusAssociative = primPlusAssociative
    plusCommutative = primPlusCommutative
    plusNeutralL = primZeroL
    plusInverseL = primNegationL


postulate primOrderReflexive : Law.reflexive PrimitiveLTE
postulate primOrderTransitive : Law.transitive PrimitiveLTE
postulate primOrderAntisymmetric : Law.antisymmetric PrimitiveLTE

public export 
implementation Preorder Integer PrimitiveLTE where
    reflexive = primOrderReflexive
    transitive = primOrderTransitive

public export 
implementation Poset Integer PrimitiveLTE where
    antisymmetric = primOrderAntisymmetric

postulate primTranslationInvariantOrderL : 
    Law.translationInvariantOrderL Trusted.primPlus PrimitiveLTE

public export 
implementation PartiallyOrderdAdditiveGroup Integer PrimitiveLTE where  
    translationInvariantOrderL = primTranslationInvariantOrderL
    translationInvariantOrderR = commuteAdditiveGroupOrderL
        PrimitiveLTE primTranslationInvariantOrderL
