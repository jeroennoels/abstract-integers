module PrimitiveInteger.Trusted

import Util.Law
import AbstractInteger.Interfaces
import Data.So
import Decidable.Order

%default total

primPlus : Binop Integer
primPlus = prim__addBigInt

export
data PrimLTE : Integer -> Integer -> Type where
    CheckLTE : So (a <= b) -> PrimLTE a b


postulate primPlusAssociative : Law.associative Trusted.primPlus
postulate primPlusCommutative : Law.commutative Trusted.primPlus
postulate primZeroL : Law.neutralL Trusted.primPlus 0
postulate primNegationL : Law.inverseL Trusted.primPlus 0 negate
postulate primOrderReflexive : Law.reflexive PrimLTE
postulate primOrderTransitive : Law.transitive PrimLTE
postulate primOrderAntisymmetric : Law.antisymmetric PrimLTE
postulate primTranslateOrderL : Law.translateOrderL Trusted.primPlus PrimLTE


public export
implementation AdditiveGroup Integer where
    add = prim__addBigInt
    zero = 0
    neg = prim__subBigInt 0
    plusAssociative = primPlusAssociative
    plusCommutative = primPlusCommutative
    plusNeutralL = primZeroL
    plusInverseL = primNegationL

public export 
implementation Preorder Integer PrimLTE where
    reflexive = primOrderReflexive
    transitive = primOrderTransitive

public export 
implementation Poset Integer PrimLTE where
    antisymmetric = primOrderAntisymmetric

public export 
implementation PartiallyOrderdAdditiveGroup Integer PrimLTE where  
    translateOrderL = primTranslateOrderL
    translateOrderR = commuteAdditiveGroupOrderL PrimLTE primTranslateOrderL
