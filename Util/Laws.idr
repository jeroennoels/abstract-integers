module Util.Laws

import public Util.Common

%default total
%access public export

parameters (rel : Rel s)

    reflexive : Type
    reflexive = (x : _) -> rel x x

    transitive : Type
    transitive = (x, y, z : _) -> rel x y -> rel y z -> rel x z

    antisymmetric : Type
    antisymmetric = (x, y : _) -> rel x y -> rel y x -> x = y


parameters ((#) : Binop s)
    infixl 8 #

    associative : Type
    associative = (x, y, z : _) -> x # (y # z) = (x # y) # z

    commutative : Type
    commutative = (x, y : _) -> x # y = y # x

    leftNeutral : s -> Type
    leftNeutral e = (x : _) -> e # x = x

    rightNeutral : s -> Type
    rightNeutral e = (x : _) -> x # e = x

    leftInverse : (s -> s) -> s -> Type
    leftInverse inv e = (x : _) -> inv x # x = e

    rightInverse : (s -> s) -> s -> Type
    rightInverse inv e = (x : _) -> x # inv x = e

    commutativeNeutral : commutative -> leftNeutral e -> rightNeutral e
    commutativeNeutral {e} comm left x = comm x e `trans` left x

    commutativeInverse : commutative -> leftInverse inv e -> rightInverse inv e
    commutativeInverse {inv} comm left x = comm x (inv x) `trans` left x

    parameters ((<) : Rel s)

        orderTranslationInvariantL : Type
        orderTranslationInvariantL = (x,y,a : _) -> x < y -> a # x < a # y

        orderTranslationInvariantR : Type
        orderTranslationInvariantR = (x,y,a : _) -> x < y -> x # a < y # a
