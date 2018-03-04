# Abstract Integers

This package aims to provide a set of abstract interfaces for integer
arithmetic.

This abstraction boundary enables you to prove properties of your
computations, based on integer arithmetic but independent of the
actual integer model that you eventually pick to run them.  So if you
need a high level of certification you can use inductive or binary
integer implementations.  Or you may simply choose to trust idris
primitive integers, and express that trust in postulates.
