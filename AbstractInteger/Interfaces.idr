module AbstractInteger.Interfaces

import Util.Common
import Util.Law

%default total
%access public export

interface Additive s where
    add : Binop s
    zero : s
    neg : s -> s
    plusAssociative : Law.associative add
    plusCommutative : Law.commutative add    
    plusNeutralL : Law.neutralL add zero
    plusNeutralR : Law.neutralR add zero
    plusInverseL : Law.inverseL add zero neg
    plusInverseR : Law.inverseR add zero neg
    -- default implementations
    plusNeutralR = Law.commuteNeutralL add zero plusCommutative plusNeutralL
    plusNeutralL = Law.commuteNeutralR add zero plusCommutative plusNeutralR
    plusInverseR = Law.commuteInverseL add zero neg plusCommutative plusInverseL
    plusInverseL = Law.commuteInverseR add zero neg plusCommutative plusInverseR

        
-- import public Decidable.Order

-- public export 
-- interface (VerifiedSemigroup g, Poset g po) =>
--   PartiallyOrderedSemigroup g (po : g -> g -> Type)
-- where
--   orderTranslationInvariantL : Law.orderTranslationInvariantL (<+>) po
--   orderTranslationInvariantR : Law.orderTranslationInvariantR (<+>) po
-- 
-- interface PartiallyOrderedSemigroup g po =>
--   IntegerDomain g (po : g -> g -> Type)
