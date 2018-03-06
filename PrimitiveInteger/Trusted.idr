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


postulate primPlusAssociative : isAssociative Trusted.primPlus
postulate primPlusCommutative : isCommutative Trusted.primPlus
postulate primZeroL : isNeutralL Trusted.primPlus 0
postulate primNegationL : isInverseL Trusted.primPlus 0 negate
postulate primOrderReflexive : isReflexive PrimLTE
postulate primOrderTransitive : isTransitive PrimLTE
postulate primOrderAntisymmetric : isAntisymmetric PrimLTE
postulate primTranslateOrderL : isTranslationInvariantL Trusted.primPlus PrimLTE


public export
implementation AdditiveGroup Integer where
    (|+|) = prim__addBigInt
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
implementation PartiallyOrderedAdditiveGroup Integer PrimLTE where
    translateOrderL = primTranslateOrderL
    translateOrderR = commuteAdditiveGroupOrderL PrimLTE primTranslateOrderL
