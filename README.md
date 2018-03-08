# bv-sized

This library defines a BitVector datatype that is parameterized by the vector
width.

It is especially useful in applications where bit vectors of
pre-specified lengths will be concatenated/truncated/extracted in such a way
that the width of everything will be known at compile time.
