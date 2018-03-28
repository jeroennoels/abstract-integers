module AbstractInteger.Theory

import public Util.Common
import public AbstractInteger.Interfaces
import public AbstractInteger.Additive
import public AbstractInteger.OrderedAdditive
import public AbstractInteger.Interval
import public AbstractInteger.EmbedNat

%access export
%default total


semiRangeToSymRange : PartiallyOrderedAdditiveGroup s rel =>
    .rel b a -> Interval rel (neg a) b -> SymRange rel a
semiRangeToSymRange {rel} {a} {b} ba (Between x pp qq) =
    Between x pp (transitive x b a qq ba)


public export
data Carry = M | O | P


onePlusCarry : IntegerDomain s loe => Carry -> Interval loe (nat 0) (nat 2)
onePlusCarry M = natInterval 0 _ _
onePlusCarry O = natInterval 1 _ _
onePlusCarry P = natInterval 2 _ _


rewriteInterval : PartiallyOrderedAdditiveGroup s rel =>
    Interval rel (neg (u |+| u) |+| u |+| a) (neg u |+| u |+| b) ->
    Interval rel (neg u |+| a) b
rewriteInterval {u} {b} (Between x lo hi) = Between x
    (rewrite sym (negatePlusPlus u u) in lo)
    (rewrite sym (plusInversePlusL b u) in hi)


rewriteIntervalBis : IntegerDomain s loe =>
    Interval loe (a |+| nat 0) b -> Interval loe a b
rewriteIntervalBis {s} {a} (Between x p q) = Between x
    (rewrite sym (plusNatZ a) in p) q


carry : IntegerDomain s loe => (u : s) -> loe (nat 2) u ->
    SymRange loe (u |+| u) -> Carry -> SymRange loe u
carry u moreThanTwo x c =
  case splitIntervalL (neg u) x of
    Left y => let y1 = shiftInterval u y
                  y2 = plusOnIntervals y1 (onePlusCarry c)
                  y3 = rewriteIntervalBis (rewriteInterval y2)
              in semiRangeToSymRange moreThanTwo y3
    Right y =>
      case splitIntervalR u y of
        Left z => ?middle
        Right z => ?right
