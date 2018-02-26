module PrimitiveInteger.Ring

import Control.Algebra

%default total
%access public export

Semigroup Integer
  where (<+>) = (+)

Monoid Integer
  where neutral = 0

Group Integer
  where inverse x = -x
