module AbstractInteger.Additive

import Util.Common
import AbstractInteger.Interfaces

%default total

public export
translateL : AdditiveGroup s => s -> s -> s
translateL a x = a |+| x

public export
translateR : AdditiveGroup s => s -> s -> s
translateR a x = x |+| a


export
plusPlusInverseL : AdditiveGroup s => .(a,b : s) -> a |+| neg b |+| b = a
plusPlusInverseL a b = qed where

    o1 : neg b |+| b = Zero
    o1 = plusInverseL b

    o2 : a |+| (neg b |+| b) = a |+| Zero
    o2 = cong {f = translateL a} o1

    o3 : a |+| (neg b |+| b) = a
    o3 = o2 `trans` plusNeutralR a

    qed = sym (plusAssoc a _ b) `trans` o3


export
plusPlusInverseR : AdditiveGroup s => .(a,b : s) -> a |+| b |+| neg b = a
plusPlusInverseR a b = qed where

    o1 : b |+| neg b = Zero
    o1 = plusInverseR b

    o2 : a |+| (b |+| neg b) = a |+| Zero
    o2 = cong {f = translateL a} o1

    o3 : a |+| (b |+| neg b) = a
    o3 = o2 `trans` plusNeutralR a

    qed = sym (plusAssoc a b _) `trans` o3


export
plusInversePlusL : AdditiveGroup s => .(a,b : s) -> neg b |+| b |+| a = a
plusInversePlusL a b = qed where

    o1 : neg b |+| b = Zero
    o1 = plusInverseL b

    o2 : neg b |+| b |+| a = Zero |+| a
    o2 = cong {f = translateR a} o1

    qed = o2 `trans` plusNeutralL a


export
plusInversePlusR : AdditiveGroup s => .(a,b : s) -> b |+| neg b |+| a = a
plusInversePlusR a b = qed where

    o1 : b |+| neg b = Zero
    o1 = plusInverseR b

    o2 : b |+| neg b |+| a = Zero |+| a
    o2 = cong {f = translateR a} o1

    qed = o2 `trans` plusNeutralL a


export
uniqueInverse : AdditiveGroup s => .(a,b : s) -> a |+| b = Zero -> neg a = b
uniqueInverse a b given = qed where

    o1 : neg a |+| (a |+| b) = neg a |+| Zero
    o1 = cong given

    o2 : neg a |+| (a |+| b) = b
    o2 = plusAssoc _ a b `trans` plusInversePlusL b a

    o3 : neg a |+| Zero = b
    o3 = sym o1 `trans` o2

    qed = sym (plusNeutralR _) `trans` o3


export
negatePlus : AdditiveGroup s => .(a,b : s) -> neg (a |+| b) = neg b |+| neg a
negatePlus a b = qed where
    o1 : b |+| (neg b |+| neg a) = neg a
    o1 = plusAssoc b _ _ `trans` plusInversePlusR _ b

    o2 : a |+| (b |+| (neg b |+| neg a)) = a |+| neg a
    o2 = cong {f = translateL a} o1

    o3 : (a |+| b) |+| (neg b |+| neg a) = Zero
    o3 = sym (plusAssoc a b _) `trans` (o2 `trans` plusInverseR a)

    qed = uniqueInverse _ _ o3


export
negatePlusAbelian : AdditiveGroup s => .(a,b : s) ->
    neg (a |+| b) = neg a |+| neg b
negatePlusAbelian a b =
    cong {f = neg} (plusCommutes a b) `trans` negatePlus b a


export
negatePlusPlus : AdditiveGroup s => .(a,b : s) -> neg (a |+| b) |+| a = neg b
negatePlusPlus a b = let
    o1 = the
       (neg (a |+| b) |+| a = neg b |+| neg a |+| a)
       (cong {f = translateR a} (negatePlus a b))
    in o1 `trans` plusPlusInverseL _ a


export
negateZero : AdditiveGroup s => neg {s} Zero = Zero
negateZero = uniqueInverse Zero Zero (plusNeutralL Zero)
