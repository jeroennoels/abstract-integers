module AbstractInteger.Lemma

import Util.Common
import AbstractInteger.Interfaces


%default total
%access export

translateL : AdditiveGroup s => s -> s -> s
translateL a x = a |+| x

translateR : AdditiveGroup s => s -> s -> s
translateR a x = x |+| a


plusPlusInverseL : AdditiveGroup s => .(a,b : s) -> a |+| neg b |+| b = a
plusPlusInverseL a b = let
    o1 = the
        (neg b |+| b = Zero)
        (plusInverseL b)
    o2 = the
        (a |+| (neg b |+| b) = a |+| Zero)
        (cong {f = translateL a} o1)
    o3 = the
        (a |+| (neg b |+| b) = a)
        (o2 `trans` plusNeutralR a)
    in sym (plusAssoc a _ b) `trans` o3


plusPlusInverseR : AdditiveGroup s => .(a,b : s) -> a |+| b |+| neg b = a
plusPlusInverseR a b = let
    o1 = the
        (b |+| neg b = Zero)
        (plusInverseR b)
    o2 = the
        (a |+| (b |+| neg b) = a |+| Zero)
        (cong {f = translateL a} o1)
    o3 = the
        (a |+| (b |+| neg b) = a)
        (o2 `trans` plusNeutralR a)
    in sym (plusAssoc a b _) `trans` o3


plusInversePlusR : AdditiveGroup s => .(a,b : s) -> b |+| (neg b |+| a) = a
plusInversePlusR a b = let
    o1 = the
        (b |+| neg b = Zero)
        (plusInverseR b)
    o2 = the
        (b |+| neg b |+| a = Zero |+| a)
        (cong {f = translateR a} o1)
    o3 = the
        (b |+| neg b |+| a = a)
        (o2 `trans` plusNeutralL a)
    in plusAssoc b _ a `trans` o3


plusInversePlusL : AdditiveGroup s => .(a,b : s) -> neg b |+| (b |+| a) = a
plusInversePlusL a b = let
    o1 = the
        (neg b |+| b = Zero)
        (plusInverseL b)
    o2 = the
        (neg b |+| b |+| a = Zero |+| a)
        (cong {f = translateR a} o1)
    o3 = the
        (neg b |+| b |+| a = a)
        (o2 `trans` plusNeutralL a)
    in plusAssoc _ b a `trans` o3


uniqueInverse : AdditiveGroup s => .(a,b : s) ->
    a |+| b = Zero -> neg a = b
uniqueInverse a b given = let
    o1 = the
        (neg a |+| (a |+| b) = neg a |+| Zero)
        (cong given)
    o2 = the
        (neg a |+| (a |+| b) = b)
        (plusInversePlusL b a)
    o3 = the
        (neg a |+| Zero = b)
        (sym o1 `trans` o2)
    qed = the
        (neg a = b)
        (sym (plusNeutralR _) `trans` o3)
    in qed


negatePlus : AdditiveGroup s => .(a,b : s) ->
    neg (a |+| b) = neg b |+| neg a
negatePlus a b = let
    o1 = the
        (b |+| (neg b |+| neg a) = neg a)
        (plusInversePlusR _ b)
    o2 = the
        (a |+| (b |+| (neg b |+| neg a)) = a |+| neg a)
        (cong {f = translateL a} o1)
    o3 = the
        ((a |+| b) |+| (neg b |+| neg a) = Zero)
        (sym (plusAssoc a b _) `trans` (o2 `trans` plusInverseR a))
    in uniqueInverse _ _ o3


negatePlusAbelian : AdditiveGroup s => .(a,b : s) ->
    neg (a |+| b) = neg a |+| neg b
negatePlusAbelian a b =
    cong {f = neg} (plusCommutes a b) `trans` negatePlus b a


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
