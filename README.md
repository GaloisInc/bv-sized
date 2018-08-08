bv-sized - A Haskell library for manipulating width-parameterized bitvectors
===

copyright (c) Ben Selfridge, Galois Inc. 2018

This library defines a `BitVector` datatype that is parameterized by the vector
width.

Requirements
===

The following are a list of mandatory and secondary requirements for bv-sized.

Mandatory Requirements
===

- Must support integer arithmetic on bitvectors of arbitrary width, assuming a
  two's-complement representation.

- Must support the construction of symbolic expressions involving bitvectors,
  and evaluating those expressions in such a way that the "pure" bitvector
  expression language can be embedded in a larger expression language. (See
  Data.BitVector.Sized.App)

- Declarative descriptions of bit encodings within an instruction word for the
  purposes of ISA definitions and the like. (See Data.BitVector.Sized.BitLayout)

Secondary Requirements
===

None.

Current Status
===

The library is relatively stable and supports all the above requirements.

Other information
===

* contact: benselfridge@galois.com
