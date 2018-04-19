# bv-sized

## Overview

This library defines a `BitVector` datatype that is parameterized by the vector width.

## Additional features

### BitLayout

We also provides a module called `BitLayout`, which is handy for defining mappings
from smaller `BitVector`s into larger ones. This module is particularly useful when
defining encodings in an instruction set.

### App

To aid in building expression languages over `BitVector`s, we provide a module called
App, which supports combining expressions over `BitVector`s using the `BitVector`
operations and evaluating said expressions. It can be used in a pure context or in
conjunction with a state monad. This module was inspired by the `App` type in
[macaw](https://github.com/GaloisInc/macaw), Galois's binary analysis framework.
