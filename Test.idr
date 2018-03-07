module Test

import AbstractInteger.Theory
import PrimitiveInteger.Trusted

abstractFoo : AdditiveGroup s => s -> s
abstractFoo x = neg x |+| x |+| zero |+| x

foo : Integer -> Integer
foo x = abstractFoo x

main : IO ()
main = do x <- getLine
          print (foo (cast x))
