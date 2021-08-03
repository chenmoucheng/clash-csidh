module Radix2 where

import           Prelude
import           Data.Bits          (Bits(..))
import           Data.Proxy         (Proxy(..))
import           GHC.TypeLits       (KnownNat, natVal)
import           GHC.TypeLits.Extra (CLog, FLog, Log)
import           GHC.TypeNats       (type (-), type (<=))

import           Clash.Prelude      (BitPack(..))

-- $

floorDivBy :: forall r t. (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, BitPack t) => t -> Proxy r -> t
floorDivBy x _ = unpack $ pack x `shiftR` fromInteger (natVal @(Log 2 r) Proxy)

modulo :: forall r t. (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, BitPack t) => t -> Proxy r -> t
modulo x _ = unpack $ pack x .&. fromInteger (natVal @(r - 1) Proxy)

multBy :: forall r t. (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, BitPack t) => t -> Proxy r -> t
multBy x _ = unpack $ pack x `shiftL` fromInteger (natVal @(Log 2 r) Proxy)
