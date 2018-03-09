# Abstract Integers

This package aims to provide an abstract interface for integer
arithmetic in Idris.

This abstraction boundary enables you to prove properties of
computations based on integer arithmetic, but independent of the
actual model that you eventually pick to run them.  If you need a high
level of certification you can use an inductive or binary integer
implementation.  Or you may simply choose to trust Idris primitive
integers, and express that trust in postulates.
