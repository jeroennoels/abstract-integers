module Util.Law

import public Util.Common

%default total
%access public export

infixl 8 #

associative : Binop s -> Type
associative (#) = (x,y,z : _) -> x # (y # z) = (x # y) # z

commutative : Binop s -> Type
commutative (#) = (x,y : _) -> x # y = y # x

neutralL : Binop s -> s -> Type
neutralL (#) e = (x : _) -> e # x = x

neutralR : Binop s -> s -> Type
neutralR (#) e = (x : _) -> x # e = x

inverseL : Binop s -> s -> (s -> s) -> Type
inverseL (#) e inv = (x : _) -> inv x # x = e

inverseR : Binop s -> s -> (s -> s) -> Type
inverseR (#) e inv = (x : _) -> x # inv x = e


commuteNeutralL : (op : Binop s) -> (e : s) ->
    commutative op -> neutralL op e -> neutralR op e
commuteNeutralL op e comm left x = comm x e `trans` left x

commuteInverseL : (op : Binop s) -> (e : s) -> (inv : s -> s) ->
    commutative op -> inverseL op e inv -> inverseR op e inv
commuteInverseL op e inv comm left x = comm x (inv x) `trans` left x


reflexive : Rel s -> Type
reflexive rel = (x : _) -> rel x x

transitive : Rel s -> Type
transitive rel = (x,y,z : _) -> rel x y -> rel y z -> rel x z

antisymmetric : Rel s -> Type
antisymmetric rel = (x,y : _) -> rel x y -> rel y x -> x = y

translateOrderL : Binop s -> Rel s -> Type
translateOrderL (#) (<) = (x,y,a : _) -> x < y -> a # x < a # y

translateOrderR : Binop s -> Rel s -> Type
translateOrderR (#) (<) = (x,y,a : _) -> x < y -> x # a < y # a


commuteTranslateOrderL : (op : Binop s) -> (rel : Rel s) ->
    commutative op -> translateOrderL op rel -> translateOrderR op rel
commuteTranslateOrderL op rel commute left x y a = 
    rewrite commute x a in
    rewrite commute y a in left x y a
