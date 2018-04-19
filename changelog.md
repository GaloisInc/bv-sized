# Changelog for [`bv-sized` package](http://hackage.haskell.org/package/bv-sized)

## 0.4.0 *April 2018*
  * Added App module for BitVector expression languages and evaluation

## 0.3.0 *April 2018*
  * fixed bug with bvShiftR, it was doing a left shift!
  * Division now rounds to zero for negative integers, bvDiv -> bvQuot
  * added Ix instance for BitVector w
  * added bv0, zero-width vector
  * bvConcatMany, bvGetBytesU (conversion to/from list of bytes)

## 0.2.1 *March 2018*
  * bvMulFSU
  * bvDivU, bvDivS
  * Added Read instance, fixed Show to be compatible. Using prettyclass for
    pretty printing. (I guess this is semi-breaking, but whatever.)

## 0.2 *March 2018*
  * bv -> bitVector, so this is very much a breaking change
  * bvShiftL, bvShiftRL, bvShiftRA
  * bvLTU, bvLTS

## 0.1.1.1 *March 2018*
  * added BitLayout

## 0.1.1.0 *March 2018*
  * added functions `bvMulFS`/`bvMulFU` for full bitvector multiplication
    without truncation
  * removed Internal module, now export all those functions in Data.BitVector.Sized
  * fixed the bv*WithRepr functions, which were not truncating the inputs properly

## 0.1.0.0 *March 2018*
  * First release
