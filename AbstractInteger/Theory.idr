module AbstractInteger.Theory

import public AbstractInteger.Interfaces
import public Util.Common

%default total

plusPreservesOrder : PartiallyOrderedAdditiveGroup g po => (a,b,c,d : g) ->
    po a b -> po c d -> a |+| c `po` b |+| d
plusPreservesOrder a b c d ab cd =
  let pp = translateOrderR a b c ab
      qq = translateOrderL c d b cd
  in transitive (a |+| c) _ _ pp qq


plusOnIntervals : PartiallyOrderedAdditiveGroup g po => 
    Interval po a b -> Interval po c d -> 
    Interval po (a |+| c) (b |+| d)
plusOnIntervals (Between x ax xb) (Between y cy yd) = let 
    pp = plusPreservesOrder _ x _ y ax cy
    qq = plusPreservesOrder x _ y _ xb yd
    in Between (x |+| y) pp qq
