module AbstractInteger.Theory

import public AbstractInteger.Interfaces

%default total

partialOrderCompose : PartiallyOrderedAdditiveGroup g po => (a,b,c,d : g) ->
    po a b -> po c d -> a |+| c `po` b |+| d
partialOrderCompose a b c d ab cd =
  let pp = translateOrderR a b c ab
      qq = translateOrderL c d b cd
  in transitive (a |+| c) _ _ pp qq

