# bv-sized

This library defines a BitVector datatype that is parameterized by the vector
width.

It is especially useful in applications where the length of every individual bit
vector will be known at compile time. Supports width-changing operations like
truncation, signed/unsigned extension, and extraction/bit slicing.
