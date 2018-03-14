module Main

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

testOrder : (a,b : Integer) -> Alt (PrimLTE (a+1) b) (PrimLTE b a)
testOrder a b = exclusiveOrder {lessOrEq = PrimLTE} a b

lala : (a,b : Integer) -> String
lala a b = case testOrder a b of
   Aaa _ => "Left"
   Bbb _ => "Right"

main : IO ()
main = do x <- getLine
          y <- getLine
          putStrLn $ show (test (cast x) (cast y))
