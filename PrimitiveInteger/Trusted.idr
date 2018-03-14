module PrimitiveInteger.Trusted

import Util.Law
import AbstractInteger.Interfaces
import Data.So
import Decidable.Order

%default total

||| Synonym to avoid implicit binding in types.
private
PrimAdd : Binop Integer
PrimAdd = prim__addBigInt

export
data PrimLTE : Integer -> Integer -> Type where
    CheckLTE : So (a <= b) -> PrimLTE a b
    CheckGT : So (not (a <= b)) -> PrimLTE b a

public export
assertPrimLTE : (a,b : Integer) -> Maybe (PrimLTE a b)
assertPrimLTE a b = case choose (a <= b) of
    Left oh => Just (CheckLTE oh)
    Right _ => Nothing


orderPrimLTE : (a,b : Integer) -> Either (PrimLTE a b) (PrimLTE b a)
orderPrimLTE a b = case choose (a <= b) of
    Left oh => Left (CheckLTE oh)
    Right oh => Right (CheckGT oh)


postulate primPlusAssociative : isAssociative PrimAdd
postulate primPlusCommutative : isCommutative PrimAdd
postulate primZeroL : isNeutralL PrimAdd 0
postulate primNegationL : isInverseL PrimAdd 0 negate
postulate primOrderReflexive : isReflexive PrimLTE
postulate primOrderTransitive : isTransitive PrimLTE
postulate primOrderAntisymmetric : isAntisymmetric PrimLTE
postulate primTranslateOrderL : isTranslationInvariantL PrimAdd PrimLTE
postulate plusOnePrimLTE : PrimLTE a b -> Not (a = b) -> PrimAdd a 1 `PrimLTE` b


public export
implementation AdditiveGroup Integer where
    (|+|) = prim__addBigInt
    Zero = 0
    neg = prim__subBigInt 0
    plusAssoc = primPlusAssociative
    plusCommutes = primPlusCommutative
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
    translateOrderR = commuteTranslationInvariantL 
        PrimAdd PrimLTE plusCommutes primTranslateOrderL


public export
implementation Ordered Integer PrimLTE where
    order = orderPrimLTE

public export
implementation Ring Integer where
    One = 1

public export
implementation IntegerDomain Integer PrimLTE where
    plusOneLessOrEq = plusOnePrimLTE
