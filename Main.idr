module Main

import Util.LocalContrib
import public AbstractInteger.Theory
import public PrimitiveInteger.Trusted

abstractFoo : AdditiveGroup s => s -> s
abstractFoo x = neg x |+| x |+| Zero |+| x |+| x

foo : Integer -> Integer
foo x = abstractFoo x  -- eta reduction leads to different runtime

double : AdditiveGroup s => s -> s
double x = x |+| x

expBase2 : AdditiveGroup s => Nat -> s -> s
expBase2 Z x = x
expBase2 (S k) x = expBase2 k (double x)

doubleInRange : PartiallyOrderedAdditiveGroup s rel => .{u : s} ->
    SymRange rel u -> SymRange rel (double u)
doubleInRange x = addInRange x x

doubleIterated : PartiallyOrderedAdditiveGroup s rel => .{u : s} ->
    (n : Nat) -> SymRange rel u -> SymRange rel (expBase2 n u)
doubleIterated Z x = x
doubleIterated (S k) x = doubleIterated k (doubleInRange x)

invokeAbstract : Nat -> SymRange PrimLTE 1000 -> Integer
invokeAbstract k x = fromInterval (doubleIterated k x)

test : Nat -> Integer -> Maybe Integer
test k n = liftA (invokeAbstract k) (inSymRange assertPrimLTE n 1000)

prim : Nat -> Integer -> Integer
prim Z x = x
prim (S k) x = prim k (x+x)

testOrder : (a,b : Integer) -> EitherErased (PrimLTE (a+1) b) (PrimLTE b a)
testOrder a b = exclusiveOrder {loe = PrimLTE} a b

split : (a,b,c : Integer) -> Interval PrimLTE a b -> 
    Either (Interval PrimLTE a (c + (-1)))
           (Interval PrimLTE c b)
split a b c i = splitIntervalR a b c i


testSplit : (b,c,x : Integer) -> String
testSplit b c x = case inSymRange assertPrimLTE x b of
    Just i => case split (-b) b c i of
                Left _ => "Left"
                Right _ => "Right"
    Nothing => "Nothing"            


lala : (a,b : Integer) -> String
lala a b = case testOrder a b of
   LeftErased _ => "Left"
   RightErased _ => "Right"

main : IO ()
main = do b <- getLine
          c <- getLine 
          x <- getLine
          putStrLn $ testSplit (cast b) (cast c) (cast x)
