module AbstractInteger.Lemma

import Util.Common
import AbstractInteger.Interfaces

%default total
%access public export

uniqueInverse : AdditiveGroup s => .(a,b : s) ->
    a |+| b = Interfaces.zero -> b = neg a
    
negatePlus : AdditiveGroup s => .(a,b : s) ->
    neg (a |+| b) = neg a |+| neg b
