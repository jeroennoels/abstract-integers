module AbstractInteger.OrderedAdditive

import Util.Common
import Util.LocalContrib
import AbstractInteger.Interfaces
import AbstractInteger.Additive

%default total


export
orderPlusMinus : PartiallyOrderedAdditiveGroup s rel => .(a,b,c : s) ->
    a |+| c `rel` b -> a `rel` b |+| neg c
orderPlusMinus {s} {rel} a b c given = qed where

    o1 : s
    o1 = a |+| c

    o2 : a |+| c |+| neg c `rel` b |+| neg c
    o2 = translateOrderR o1 b (neg c) given

    o3 : a |+| c |+| neg c = a
    o3 = plusPlusInverseR a c

    qed = rewrite sym o3 in o2


export
negationReversesOrder : PartiallyOrderedAdditiveGroup s rel => .(a,b : s) ->
    .rel a b -> neg b `rel` neg a
negationReversesOrder {rel} a b given = qed where

    o1 : neg a |+| a `rel` neg a |+| b
    o1 = translateOrderL _ _ (neg a) given

    o2 : neg a |+| a |+| neg b `rel` neg a |+| b |+| neg b
    o2 = translateOrderR _ _ (neg b) o1

    o3 : neg a |+| a |+| neg b = neg b
    o3 = plusInversePlusL _ a

    o4 : neg a |+| b |+| neg b = neg a
    o4 = plusPlusInverseR _ b

    qed = rewriteRelation rel o3 o4 o2


export
plusPreservesOrder : PartiallyOrderedAdditiveGroup s rel => .(a,b,c,d : s) ->
    .rel a b -> .rel c d -> rel (a |+| c) (b |+| d)
plusPreservesOrder a b c d ab cd =
    let pp = translateOrderR a b c ab
        qq = translateOrderL c d b cd
    in transitive (a |+| c) _ _ pp qq


||| Decide whether @a < @b or @a >= @b.
export
exclusiveOrder : IntegerDomain s loe => (a,b : s) ->
    EitherErased (a |+| One `loe` b) (b `loe` a)
exclusiveOrder {loe} a b =
  case order {to = loe} a b of
    Left ab => case decEq a b of
        Yes Refl => RightErased (reflexive a)
        No contra => LeftErased (plusOneLessOrEq ab contra)
    Right ba => RightErased ba
