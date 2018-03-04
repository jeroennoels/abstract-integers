module PrimitiveInteger.Trusted

import Util.Law
import AbstractInteger.Interfaces

%default total

primPlus : Binop Integer
primPlus = prim__addBigInt

postulate primPlusAssociative : Law.associative Trusted.primPlus
postulate primPlusCommutative : Law.commutative Trusted.primPlus
postulate primZeroL : Law.neutralL Trusted.primPlus 0
postulate primNegationL : Law.inverseL Trusted.primPlus 0 negate

public export
implementation Additive Integer where
  add = prim__addBigInt
  zero = 0
  neg = prim__subBigInt 0
  plusAssociative = primPlusAssociative
  plusCommutative = primPlusCommutative
  plusNeutralL = primZeroL
  plusInverseL = primNegationL


-- import Data.So
-- import Decidable.Order

-- data PrimitiveOrder : Integer -> Integer -> Type where
--   CheckPrimitiveOrder : So (a <= b) -> PrimitiveOrder a b
-- 
-- postulate orderReflexive : Law.reflexive PrimitiveOrder
-- postulate orderTransitive : Law.transitive PrimitiveOrder
-- postulate orderAntisymmetric : Law.antisymmetric PrimitiveOrder
-- 
-- 
-- postulate orderPlusInvariantL : 
--   Law.orderTranslationInvariantL (+) PrimitiveOrder
--   
-- postulate orderPlusInvariantR : 
--   Law.orderTranslationInvariantR (+) PrimitiveOrder
-- 
-- plusRightNeutral : Law.rightNeutral (+) 0
-- plusRightNeutral = 
--   let lemma = Law.commutativeNeutral (+)
--   in lemma plusCommutative plusLeftNeutral
-- 
-- plusRightInverse : Law.rightInverse (+) inverse 0
-- plusRightInverse = 
--   let lemma = Law.commutativeInverse (+)
--   in lemma plusCommutative plusLeftInverse
-- 
-- 
-- Preorder Integer PrimitiveOrder where
--   reflexive = orderReflexive
--   transitive = orderTransitive
-- 
-- Poset Integer PrimitiveOrder where
--   antisymmetric = orderAntisymmetric
-- 
-- VerifiedSemigroup Integer where
--   semigroupOpIsAssociative = plusAssociative
-- 
-- VerifiedMonoid Integer where
--   monoidNeutralIsNeutralL = plusRightNeutral
--   monoidNeutralIsNeutralR = plusLeftNeutral
-- 
-- VerifiedGroup Integer where
--   groupInverseIsInverseL = plusRightInverse
--   groupInverseIsInverseR = plusLeftInverse
-- 
-- PartiallyOrderedSemigroup Integer PrimitiveOrder where
--   orderTranslationInvariantL = orderPlusInvariantL
--   orderTranslationInvariantR = orderPlusInvariantR
