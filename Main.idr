module Main

import AbstractInteger.Theory
import PrimitiveInteger.Trusted

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
    SymRange {rel} u -> SymRange {rel} (double u)
doubleInRange x = addInRange x x

doubleIterated : PartiallyOrderedAdditiveGroup s rel => .{u : s} ->
    (n : Nat) -> SymRange {rel} u -> SymRange {rel} (expBase2 n u)
doubleIterated Z x = x
doubleIterated (S k) x = doubleIterated k (doubleInRange x)

invokeAbstract : Nat -> SymRange {rel = PrimLTE} 1000 -> Integer
invokeAbstract k x = fromInterval (doubleIterated k x)

test : Nat -> Integer -> Maybe Integer
test k n = liftA (invokeAbstract k) (inSymRange n 1000)

prim : Nat -> Integer -> Integer
prim Z x = x
prim (S k) x = prim k (x+x)

main : IO ()
main = do x <- getLine
          putStrLn $ show (test (cast x) (cast x))
