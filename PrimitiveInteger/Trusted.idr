module PrimitiveInteger.Trusted

import Util.Law
import AbstractInteger.Interfaces
import Data.So
import Decidable.Order

%default total

||| Synonym to avoid implicit binding in types.
AddBigInt : Binop Integer
AddBigInt = prim__addBigInt

export
data PrimLTE : Integer -> Integer -> Type where
    CheckLTE : So (a <= b) -> PrimLTE a b
    CheckGT : So (not (a <= b)) -> PrimLTE b a

primLTE : (a,b : Integer) -> Maybe (PrimLTE a b)
primLTE a b = case choose (a <= b) of
    Left oh => Just (CheckLTE oh)
    Right _ => Nothing


orderPrimLTE : (a,b : Integer) -> Either (PrimLTE a b) (PrimLTE b a)
orderPrimLTE a b = case choose (a <= b) of
    Left oh => Left (CheckLTE oh)
    Right oh => Right (CheckGT oh)


postulate primPlusAssociative : isAssociative AddBigInt
postulate primPlusCommutative : isCommutative AddBigInt
postulate primZeroL : isNeutralL AddBigInt 0
postulate primNegationL : isInverseL AddBigInt 0 negate
postulate primOrderReflexive : isReflexive PrimLTE
postulate primOrderTransitive : isTransitive PrimLTE
postulate primOrderAntisymmetric : isAntisymmetric PrimLTE
postulate primTranslateOrderL : isTranslationInvariantL AddBigInt PrimLTE


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
        AddBigInt PrimLTE plusCommutes primTranslateOrderL
    maybeOrdered = primLTE


public export
implementation Ordered Integer PrimLTE where
    order = orderPrimLTE

public export
implementation Ring Integer where
    One = 1

public export
implementation IntegerDomain Integer PrimLTE where
    plusOneLessOrEq = p where 
        postulate p : PrimLTE a b -> Not (a = b) -> (AddBigInt a 1) `PrimLTE` b
