module AbstractInteger.Lemma

import Util.Common
import AbstractInteger.Interfaces

%default total
%access public export

uniqueInverse : AdditiveGroup s => .(a,b : s) ->
    a |+| b = Zero -> neg a = b
uniqueInverse a b step0 = let
    step1 = the (neg a |+| (a |+| b) = neg a |+| Zero) 
                (cong step0)
    step2 = the (neg a |+| (a |+| b) = neg a |+| a |+| b) 
                (plusAssoc (neg a) a b)
    step3 = the (neg a |+| a |+| b = neg a |+| Zero)
                (sym step2 `trans` step1)
    step4 = the (neg a |+| a |+| b = Zero |+| b)
                (cong {f = \x => x |+| b} (plusInverseL a))
    step5 = the (neg a |+| Zero = Zero |+| b) 
                (sym step3 `trans` step4) 
    step6 = the (neg a |+| Zero = b) 
                (step5 `trans` plusNeutralL b)
    in sym (plusNeutralR $ neg a) `trans` step6


negatePlus : AdditiveGroup s => .(a,b : s) ->
    neg (a |+| b) = neg a |+| neg b
