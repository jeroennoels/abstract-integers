module AbstractInteger.Lemma

import Util.Common
import AbstractInteger.Interfaces

%default total
%access public export

translateR : AdditiveGroup s => s -> s -> s
translateR b a = a |+| b 


uniqueInverse : AdditiveGroup s => .(a,b : s) ->
    a |+| b = Zero -> neg a = b
uniqueInverse a b given = let
    o1 = the 
        (neg a |+| (a |+| b) = neg a |+| Zero) 
        (cong given)
    o2 = the 
        (neg a |+| (a |+| b) = neg a |+| a |+| b) 
        (plusAssoc (neg a) a b)
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
        (sym (plusNeutralR $ neg a) `trans` o6) 
    in qed


negatePlus : AdditiveGroup s => .(a,b : s) ->
    neg (a |+| b) = neg a |+| neg b
