module AbstractInteger.Theory

import public AbstractInteger.Interfaces

%default total

partialOrderCompose : PartiallyOrderedSemigroup g po => (a,b,c,d : g) ->
  po a b -> po c d -> a <+> c `po` b <+> d
partialOrderCompose a b c d ab cd =
  let pp = orderTranslationInvariantR a b c ab
      qq = orderTranslationInvariantL c d b cd
  in transitive (a <+> c) _ _ pp qq

