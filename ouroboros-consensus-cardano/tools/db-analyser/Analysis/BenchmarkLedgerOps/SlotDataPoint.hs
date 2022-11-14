{-# LANGUAGE NamedFieldPuns #-}

module Analysis.BenchmarkLedgerOps.SlotDataPoint (
    SlotDataPoint (..)
  , showData
  , showHeaders
  ) where

import           Data.Int (Int64)
import           Data.List (intercalate)
import           Data.Word (Word32, Word64)

import           Cardano.Slotting.Slot (SlotNo)

import           Ouroboros.Consensus.Util.Condense (condense)

-- | Information about the time spent processing the block corresponding to
-- 'slot', divided into the five major operations:
--
--  0. Forecast.
--  1. Header tick.
--  2. Header application.
--  3. Block tick.
--  4. Block application.
--
-- It is up to the user of a slot data point to decide which units the data
-- represent (eg milliseconds, nanoseconds, etc)
data SlotDataPoint =
    SlotDataPoint
      { -- | Slot in which the 5 ledger operations were applied.
        slot        :: !SlotNo
        -- | Gap to the previous slot.
      , slotGap     :: !Word64
        -- | Total time spent in the 5 ledger operations at 'slot'.
      , totalTime   :: !Int64
        -- | Time spent by the mutator while performing the 5 ledger operations
        -- at 'slot'.
      , mut         :: !Int64
        -- | Time spent in garbage collection while performing the 5 ledger
        -- operations at 'slot'.
      , gc          :: !Int64
        -- | Total number of major garbage collections that took place while
        -- performing the 5 ledger operations at 'slot'.
      , majGcCount  :: !Word32
      , forecast    :: !Int64
      , headerTick  :: !Int64
      , headerApply :: !Int64
      , blockTick   :: !Int64
      , blockApply  :: !Int64
      }

-- | Return the headers that correspond to the fields of 'SlotDataPoint'.
--
-- The position of each header matches the position in which the corresponding
-- field value is returned in 'showData'. Eg, if show headers returns:
--
-- > "slot slotGap totalTime" ...
--
-- then the third value returned by 'showData' will correspond to 'totalTime'.
showHeaders :: String -> String
showHeaders =
    (`intercalate` [ "slot"
                   , "slotGap"
                   , "totalTime"
                   , "mut"
                   , "gc"
                   , "majGcCount"
                   , "forecast"
                   , "headerTick"
                   , "headerApply"
                   , "blockTick"
                   , "blockApply"
                   ]
    )

-- | See 'showHeaders'
showData :: SlotDataPoint -> String -> String
showData SlotDataPoint { slot
                       , slotGap
                       , totalTime
                       , mut
                       , gc
                       , majGcCount
                       , forecast
                       , headerTick
                       , headerApply
                       , blockTick
                       , blockApply
                       }
    =
    (`intercalate` [ condense slot
                   , show     slotGap
                   , show     totalTime
                   , show     mut
                   , show     gc
                   , show     majGcCount
                   , show     forecast
                   , show     headerTick
                   , show     headerApply
                   , show     blockTick
                   , show     blockApply
                   ]
    )
