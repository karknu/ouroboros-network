{-# OPTIONS_GHC -Wno-orphans     #-}
module Test.Ouroboros.Network.Orphans () where


import           Data.Hashable (Hashable (hashWithSalt), hashUsing)
import qualified Data.IP as IP
import           Data.Word (Word16)

import           Codec.Serialise.Class (Serialise)
import           Network.Socket (PortNumber)


instance Hashable IP.IPv4
instance Hashable IP.IPv6
instance Hashable IP.IP

instance Hashable PortNumber where
  hashWithSalt salt pn =
    hashUsing (fromIntegral :: PortNumber -> Word16) salt pn

instance Serialise IP.IPv4
instance Serialise IP.IPv6
instance Serialise IP.IP

