module PrimitiveInteger.Trusted

import Util.Laws
import PrimitiveInteger.Ring
import AbstractInteger.Interfaces

import Control.Algebra
import Data.So
import Decidable.Order
import Interfaces.Verified

%default total

data PrimitiveOrder : Integer -> Integer -> Type where
  CheckPrimitiveOrder : So (a <= b) -> PrimitiveOrder a b

postulate orderReflexive : Laws.reflexive PrimitiveOrder
postulate orderTransitive : Laws.transitive PrimitiveOrder
postulate orderAntisymmetric : Laws.antisymmetric PrimitiveOrder

postulate plusAssociative : Laws.associative (+)
postulate plusCommutative : Laws.commutative (+)
postulate plusLeftNeutral : Laws.leftNeutral (+) 0
postulate plusLeftInverse : Laws.leftInverse (+) inverse 0

postulate orderPlusInvariantL : 
  Laws.orderTranslationInvariantL (+) PrimitiveOrder
  
postulate orderPlusInvariantR : 
  Laws.orderTranslationInvariantR (+) PrimitiveOrder

plusRightNeutral : Laws.rightNeutral (+) 0
plusRightNeutral = 
  let lemma = Laws.commutativeNeutral (+)
  in lemma plusCommutative plusLeftNeutral

plusRightInverse : Laws.rightInverse (+) inverse 0
plusRightInverse = 
  let lemma = Laws.commutativeInverse (+)
  in lemma plusCommutative plusLeftInverse


Preorder Integer PrimitiveOrder where
  reflexive = orderReflexive
  transitive = orderTransitive

Poset Integer PrimitiveOrder where
  antisymmetric = orderAntisymmetric

VerifiedSemigroup Integer where
  semigroupOpIsAssociative = plusAssociative

VerifiedMonoid Integer where
  monoidNeutralIsNeutralL = plusRightNeutral
  monoidNeutralIsNeutralR = plusLeftNeutral

VerifiedGroup Integer where
  groupInverseIsInverseL = plusRightInverse
  groupInverseIsInverseR = plusLeftInverse

PartiallyOrderedSemigroup Integer PrimitiveOrder where
  orderTranslationInvariantL = orderPlusInvariantL
  orderTranslationInvariantR = orderPlusInvariantR
