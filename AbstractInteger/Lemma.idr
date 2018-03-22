module AbstractInteger.Lemma

import Util.Common
import AbstractInteger.Interfaces
import AbstractInteger.Additive

%default total
%access export


orderPlusMinus : PartiallyOrderedAdditiveGroup s rel => .(a,b,c : s) ->
    .(a |+| c `rel` b) -> a `rel` b |+| neg c
orderPlusMinus {s} {rel} a b c prf = let
    ac = the s (a |+| c)
    o1 = the
        (a |+| c |+| neg c `rel` b |+| neg c)
        (translateOrderR ac b (neg c) prf)
    o2 = the
        (a |+| c |+| neg c = a)
        (plusPlusInverseR a c)
    in rewrite sym o2 in o1


negationReversesOrder : PartiallyOrderedAdditiveGroup s rel => .(a,b : s) ->
    .rel a b -> neg b `rel` neg a
negationReversesOrder {rel} a b given = let
    o1 = the
        (neg a |+| a `rel` neg a |+| b)
        (translateOrderL _ _ (neg a) given)
    o2 = the
        (neg a |+| a |+| neg b `rel` neg a |+| b |+| neg b)
        (translateOrderR _ _ (neg b) o1)
   -- todo: annotate
    o3 = plusInversePlusL (neg b) a
    o4 = plusPlusInverseR (neg a) b   
    in rewriteRelation rel o3 o4 o2
        
        
plusPreservesOrder : PartiallyOrderedAdditiveGroup s rel => .(a,b,c,d : s) ->
    .rel a b -> .rel c d -> rel (a |+| c) (b |+| d)
plusPreservesOrder a b c d ab cd =
  let pp = translateOrderR a b c ab
      qq = translateOrderL c d b cd
  in transitive (a |+| c) _ _ pp qq

