module AbstractInteger.Lemma

import Util.Common
import AbstractInteger.Interfaces


%default total
%access export

translateL : AdditiveGroup s => s -> s -> s
translateL a x = a |+| x

translateR : AdditiveGroup s => s -> s -> s
translateR a x = x |+| a


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
    o6 = the
        (neg a |+| Zero = b)
        (sym o1 `trans` o2)
    qed = the
        (neg a = b)
        (sym (plusNeutralR _) `trans` o6)
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


orderPlusMinusOne : IntegerDomain s rel => .(a,b : s) ->
    .(a |+| One `rel` b) -> a `rel` b |+| neg One
orderPlusMinusOne {s} {rel} a b prf = let
    o1 = the s (a |+| One)
    o2 = the
        (a |+| One |+| neg One `rel` b |+| neg One)
        (translateOrderR o1 b (neg One) prf)
    o3 = the
        (a |+| One |+| neg One = a)
        (plusPlusInverseR a One)
    in rewrite sym o3 in o2
