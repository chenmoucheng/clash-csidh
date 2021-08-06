module Radix2 where

import Prelude
import Data.Bits          (Bits(..))
import Data.Proxy         (Proxy(..))
import GHC.TypeLits       (KnownNat, natVal)
import GHC.TypeLits.Extra (CLog, FLog, Log)
import GHC.TypeNats       (type (-), type (<=))

import Clash.Prelude      (BitPack(..))

-- $

floorDivBy :: forall r t. (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, BitPack t) => t -> t
floorDivBy = unpack . flip shiftR (fromInteger . natVal @(Log 2 r) $ Proxy) . pack

modulo :: forall r t. (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, BitPack t) => t -> t
modulo = unpack . (fromInteger (natVal @(r - 1) Proxy) .&.) . pack

multBy :: forall r t. (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, BitPack t) => t -> t
multBy = unpack . flip shiftL (fromInteger . natVal @(Log 2 r) $ Proxy) . pack
