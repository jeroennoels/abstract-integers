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
semiRangeToSymRange {a} {b} ba (Between x pp qq) =
    Between x pp (transitive x b a qq ba)


public export
data Carry = M | O | P

onePlusCarry : IntegerDomain s loe => Carry -> Interval loe (nat 0) (nat 2)
onePlusCarry M = natInterval 0
onePlusCarry O = natInterval 1
onePlusCarry P = natInterval 2


rewriteInterval : PartiallyOrderedAdditiveGroup s rel =>
    Interval rel (neg (u |+| u) |+| u |+| a) (neg u |+| u |+| b) ->
    Interval rel (neg u |+| a) b
rewriteInterval {u} {b} (Between x lo hi) = Between x
    (rewrite sym (negatePlusPlus u u) in lo)
    (rewrite sym (plusInversePlusL b u) in hi)


rewriteIntervalBis : PartiallyOrderedAdditiveGroup s loe =>
    Interval loe (neg a |+| b) c -> Interval loe (neg (a |+| neg b)) c
rewriteIntervalBis {a} {b} (Between x p q) =
    Between x (rewrite negatePlusNegate a b in p) q


decr : IntegerDomain s loe => s -> s
decr a = a |+| neg One


lemma : IntegerDomain s loe => .loe (nat 2) u -> loe One (decr u)
lemma {loe} {u} prf = rewriteRelation loe embedNatTwoMinusOne Refl o1
   where
    o1 : loe (nat 2 |+| neg One) (u |+| neg One)
    o1 = translateOrderR (nat 2) u (neg One) prf


carry : IntegerDomain s loe => (u : s) -> .loe (nat 2) u ->
    SymRange loe (u |+| u) -> (Carry, SymRange loe (decr u))
carry u prf x =
  case splitIntervalL (neg u) x of
    Left y => let sy = shiftInterval One $ shiftInterval u y
                  ry = rewriteIntervalBis $ rewriteInterval sy
              in (M, semiRangeToSymRange (lemma {u} prf) ry)
    Right y =>
      case splitIntervalR u y of
        Left z => ?middle
        Right z => ?right
