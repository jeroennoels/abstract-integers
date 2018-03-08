module Util.Law

import public Util.Common

%default total
%access public export

infixl 8 #

isAssociative : .Binop s -> Type
isAssociative (#) = (x,y,z : _) -> x # (y # z) = (x # y) # z

isCommutative : .Binop s -> Type
isCommutative (#) = (x,y : _) -> x # y = y # x

isNeutralL : .Binop s -> s -> Type
isNeutralL (#) e = (x : _) -> e # x = x

isNeutralR : .Binop s -> s -> Type
isNeutralR (#) e = (x : _) -> x # e = x

isInverseL : .Binop s -> s -> (s -> s) -> Type
isInverseL (#) e inv = (x : _) -> inv x # x = e

isInverseR : .Binop s -> s -> (s -> s) -> Type
isInverseR (#) e inv = (x : _) -> x # inv x = e


commuteNeutralL : .(op : Binop s) -> .(e : s) ->
    .isCommutative op -> .isNeutralL op e -> isNeutralR op e
commuteNeutralL op e comm left x = comm x e `trans` left x

commuteInverseL : .(op : Binop s) -> .(e : s) -> .(inv : s -> s) ->
    .isCommutative op -> .isInverseL op e inv -> isInverseR op e inv
commuteInverseL op e inv comm left x = comm x (inv x) `trans` left x


isReflexive : .Rel s -> Type
isReflexive rel = (x : _) -> rel x x

isTransitive : .Rel s -> Type
isTransitive rel = (x,y,z : _) -> rel x y -> rel y z -> rel x z

isAntisymmetric : .Rel s -> Type
isAntisymmetric rel = (x,y : _) -> rel x y -> rel y x -> x = y

isTranslationInvariantL : .Binop s -> .Rel s -> Type
isTranslationInvariantL (#) rel = (x,y,a : _) -> rel x y -> rel (a # x) (a # y)

isTranslationInvariantR : .Binop s -> .Rel s -> Type
isTranslationInvariantR (#) rel = (x,y,a : _) -> rel x y -> rel (x # a) (y # a)


commuteTranslationInvariantL : .(op : Binop s) -> .(rel : Rel s) ->
    isCommutative op ->
    isTranslationInvariantL op rel ->
    isTranslationInvariantR op rel
commuteTranslationInvariantL op rel commute left x y a =
    rewrite commute x a in
    rewrite commute y a in left x y a
