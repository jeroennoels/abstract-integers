module Main

import AbstractInteger.Theory
import PrimitiveInteger.Trusted

abstractFoo : AdditiveGroup s => s -> s
abstractFoo x = neg x |+| x |+| zero |+| x

foo : Integer -> Integer
foo x = abstractFoo x

test : SymRange {rel = PrimLTE} 100 -> Integer
test x = fromInterval (addInRange x x)

test2 : Integer -> Maybe Integer
test2 n = liftA test (inSymRange n 100)

main : IO ()
main = do x <- getLine
          let n = the Integer (cast x)
          print (test2 n)
