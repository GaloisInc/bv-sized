module Data.Parameterized.WidthRepr
  ( WidthRepr
  , widthRepr
  , knownWidth
  , widthNat
  , widthInt
  , widthMask
  ) where

import Data.Parameterized.NatRepr
import GHC.TypeLits (KnownNat)

data WidthRepr w = WidthRepr (NatRepr w) Integer
  deriving (Show)

-- | Construct a 'WidthRepr' from a 'NatRepr'.
widthRepr :: NatRepr w -> WidthRepr w
widthRepr n = WidthRepr n (maxUnsigned n)

-- | Construct a 'WidthRepr' from a 'KnownNat' context.
knownWidth :: KnownNat w => WidthRepr w
knownWidth = WidthRepr n (maxUnsigned n)
  where n = knownNat

-- | Get the 'NatRepr' out of a 'WidthRepr'.
widthNat :: WidthRepr w -> NatRepr w
widthNat (WidthRepr n _) = n

-- | Get the width as an 'Int'.
widthInt :: WidthRepr w -> Int
widthInt (WidthRepr n _) = widthVal n

-- | Get the mask out of a 'WidthRepr'.
widthMask :: WidthRepr w -> Integer
widthMask (WidthRepr _ mask) = mask
