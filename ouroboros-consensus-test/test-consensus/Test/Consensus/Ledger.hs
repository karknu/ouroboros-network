{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns    #-}
module Test.Consensus.Ledger (tests) where

import           Cardano.Slotting.Slot (WithOrigin (..))
import           Control.Applicative (liftA2)
import           Control.Monad (foldM)
import qualified Data.FingerTree.Strict as FT
import           Data.Foldable (foldl')
import qualified Data.List.NonEmpty as NE
import           Ouroboros.Consensus.Config.SecurityParam (SecurityParam)
import           Ouroboros.Consensus.Ledger.Basics hiding (LedgerState)
import           Ouroboros.Consensus.Storage.LedgerDB.HD
import qualified Ouroboros.Network.AnchoredSeq as AS
import           Ouroboros.Network.Block (Point (..), blockPoint)
import qualified Ouroboros.Network.Point as Point
import           Test.QuickCheck hiding (elements)
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.QuickCheck (testProperty)
import           Test.Util.TestBlock

tests :: TestTree
tests = testGroup "Ledger"
  [ testGroup "DbChangelog"
      [ testProperty "emptyDbChangelog immutableAnchored" prop_emptyDbImmutableAnchored
      , testProperty "emptyDbChangelog volatileTipAnchorsImmutable" prop_emptyDbVolatileTipAnchorsImmutable
--      , testProperty "prune changelog leaves length invariant" prop_pruneKeepsTotalLength
      ]

  ]

genAnchoredSequence :: AS.Anchorable v a a => a -> (a -> Gen a) -> Gen (AS.AnchoredSeq v a a)
genAnchoredSequence anchor genNext = sized $ \n -> do
    k <- chooseInt (0, n)
    step (pure $ AS.Empty anchor) k anchor
  where
    step !acc k x =
      if k == 0 then acc else do
        acc' <- acc
        y <- genNext x
        step (pure $ acc' AS.:> y) (k - 1) y

genPoint :: Point TestBlock -> Gen (Point TestBlock)
genPoint = pure . Point . nextPoint' . getPoint
  where
    nextPoint' Origin = At (Point.Block 1 (TestHash $ 0 NE.:| []))
    nextPoint' (At (Point.Block slotNo hash)) = At (Point.Block (succ slotNo) hash)

genTestLedgerDbChangelogState :: DbChangelogState (LedgerState TestBlock)
  -> Gen (DbChangelogState (LedgerState TestBlock))
genTestLedgerDbChangelogState (DbChangelogState ledger) = do
  point <- genPoint $ lastAppliedPoint ledger
  pure $ DbChangelogState $ ledger { lastAppliedPoint = point }

genDbChangelog :: (GetTip (l EmptyMK), TableStuff l) =>
  l EmptyMK -> (DbChangelogState l -> Gen (DbChangelogState l)) -> Gen (DbChangelog l)
genDbChangelog anchor gen = do
  imm <- genAnchoredSequence (DbChangelogState anchor) gen
  vol <- genAnchoredSequence (AS.headAnchor imm) gen
  pure $ DbChangelog
    { changelogDiffAnchor = getTipSlot anchor
    , changelogDiffs = pureLedgerTables (ApplySeqDiffMK emptySeqUtxoDiff)
    , changelogImmutableStates = imm
    , changelogVolatileStates = vol
    }

-- instance Arbitrary (LedgerState TestBlock mk) where
--   arbitrary =
--     pure $ forgetLedgerTables testInitLedger { lastAppliedPoint = Point undefined }


instance Arbitrary (DbChangelog (LedgerState TestBlock)) where
  arbitrary = genDbChangelog (forgetLedgerTables $ testInitLedger) genTestLedgerDbChangelogState

prop_emptyDbImmutableAnchored :: Property
prop_emptyDbImmutableAnchored = property $ immutableAnchored $
  emptyDbChangeLog $ forgetLedgerTables testInitLedger

prop_emptyDbVolatileTipAnchorsImmutable :: Property
prop_emptyDbVolatileTipAnchorsImmutable = property $ volatileTipAnchorsImmutable $
  emptyDbChangeLog $ forgetLedgerTables testInitLedger

prop_extendDbChangelogKeepsImmutableStates :: Int -> Property
prop_extendDbChangelogKeepsImmutableStates i = undefined

prop_pruneKeepsTotalLength :: SecurityParam -> DbChangelog (LedgerState TestBlock) -> Property
prop_pruneKeepsTotalLength sp log =
  let log' = pruneVolatilePartDbChangelog sp log
  in property $ AS.length (changelogImmutableStates log) + AS.length (changelogVolatileStates log)
     == AS.length (changelogImmutableStates log') + AS.length (changelogVolatileStates log')

immutableAnchored :: DbChangelog (LedgerState TestBlock) -> Bool
immutableAnchored DbChangelog { changelogDiffAnchor, changelogImmutableStates } =
  changelogDiffAnchor == fmap Point.blockPointSlot point
  where
    point = getPoint $ lastAppliedPoint $ unDbChangelogState $ AS.anchor $ changelogImmutableStates

volatileTipAnchorsImmutable :: DbChangelog (LedgerState TestBlock) -> Bool
volatileTipAnchorsImmutable DbChangelog { changelogImmutableStates, changelogVolatileStates } =
  AS.anchor changelogVolatileStates == AS.headAnchor changelogImmutableStates


-- | Generators:
-- Either
--  1. Via the internals <- this one!
--  2. Via the public API

-- | Invariants:
--   1. changeLogDiffAnchor is the anchor of changeLogImmutableStates
--   2. the tip of changeLogImmutableStates is the anchor of changeLogVolatileStates
--   3. something with increasing slot numbers (?)
--
-- | Combinators to test
--
-- emptyDbChangeLog
-- pruneVolatilePartDbChangelog (sic) :: GetTip (l EmptyMK) => SecurityParam -> DbChangelog l -> DbChangelog l
-- extendDbChangeLog :: (TableStuff l, GetTip (l EmptyMK)) => DbChangelog l -> l DiffMK -> DbChangelog l
-- flushDbChangelog :: => DbChangelogFlushPolicy -> DbChangelog l -> (DbChangelog l, DbChangelog l)
-- prefixDbChangelog
-- prefixBackToAnchorDbChangelog
-- rollbackDbChangelog
-- youngestImmutableSlotDbChangelog
--

