module AbstractInteger.Interfaces

import public Decidable.Order
import public Interfaces.Verified
import Util.Laws

%default total
%access public export


interface (VerifiedSemigroup g, Poset g po) =>
  PartiallyOrderedSemigroup g (po : g -> g -> Type)
where
  orderTranslationInvariantL : Laws.orderTranslationInvariantL (<+>) po
  orderTranslationInvariantR : Laws.orderTranslationInvariantR (<+>) po


interface PartiallyOrderedSemigroup g po =>
  IntegerDomain g (po : g -> g -> Type)
