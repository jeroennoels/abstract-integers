module Test

import AbstractInteger.Theory
import PrimitiveInteger.Trusted

abstractFoo : AdditiveGroup s => s -> s
abstractFoo x = neg x |+| x |+| zero

foo : Integer -> Integer
foo x = abstractFoo x

