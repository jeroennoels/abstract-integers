module AbstractInteger.Lemma

import Util.Common
import AbstractInteger.Interfaces

%default total
%access export

translateL : AdditiveGroup s => s -> s -> s
translateL a x = a |+| x

translateR : AdditiveGroup s => s -> s -> s
translateR a x = x |+| a


uniqueInverse : AdditiveGroup s => .(a,b : s) ->
    a |+| b = Zero -> neg a = b
uniqueInverse a b given = let
    o1 = the
        (neg a |+| (a |+| b) = neg a |+| Zero)
        (cong given)
    o2 = the
        (neg a |+| (a |+| b) = neg a |+| a |+| b)
        (plusAssoc _ a b)
    o3 = the
        (neg a |+| a |+| b = neg a |+| Zero)
        (sym o2 `trans` o1)
    o4 = the
        (neg a |+| a |+| b = Zero |+| b)
        (cong {f = translateR b} (plusInverseL a))
    o5 = the
        (neg a |+| Zero = Zero |+| b)
        (sym o3 `trans` o4)
    o6 = the
        (neg a |+| Zero = b)
        (o5 `trans` plusNeutralL b)
    qed = the
        (neg a = b)
        (sym (plusNeutralR _) `trans` o6)
    in qed


negatePlus : AdditiveGroup s => .(a,b : s) ->
    neg (a |+| b) = neg b |+| neg a
negatePlus a b = let
    o1 = the
        (b |+| neg b = Zero)
        (plusInverseR b)
    o2 = the
        (b |+| neg b |+| neg a = Zero |+| neg a)
        (cong {f = translateR (neg a)} o1)
    o3 = the
        (b |+| neg b |+| neg a = neg a)
        (o2 `trans` plusNeutralL _)
    o4 = the
        (b |+| (neg b |+| neg a) = neg a)
        (plusAssoc b _ _ `trans` o3)
    o5 = the
        (a |+| (b |+| (neg b |+| neg a)) = a |+| neg a)
        (cong {f = translateL a} o4)
    o6 = the
        ((a |+| b) |+| (neg b |+| neg a) = Zero)
        (sym (plusAssoc a b _) `trans` (o5 `trans` plusInverseR a))
    in uniqueInverse _ _ o6


negatePlusAbelian : AdditiveGroup s => .(a,b : s) ->
    neg (a |+| b) = neg a |+| neg b
negatePlusAbelian a b = 
    cong {f = neg} (plusCommutes a b) `trans` negatePlus b a
