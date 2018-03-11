# Changelog for [`bv-sized` package](http://hackage.haskell.org/package/bv-sized)

## 0.1.0.0 *March 2018*
  * First release

## 0.1.1.0 *March 2018*
  * added functions `bvMulFS`/`bvMulFU` for full bitvector multiplication
    without truncation
  * removed Internal module, now export all those functions in Data.BitVector.Sized
  * fixed the bv*WithRepr functions, which were not truncating the inputs properly
