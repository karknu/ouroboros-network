{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Ouroboros.Storage.LedgerDB.DbChangelog (
    run
  , tests
  ) where

import           Cardano.Slotting.Slot (WithOrigin (..))
import           Control.Monad hiding (ap)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.State.Strict hiding (state)
import qualified Data.FingerTree.Strict as FT
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (catMaybes, isJust)
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import           NoThunks.Class (NoThunks)
import           Ouroboros.Consensus.Config.SecurityParam (SecurityParam (..))
import           Ouroboros.Consensus.Ledger.Basics hiding (LedgerState)
import           Ouroboros.Consensus.Storage.LedgerDB.HD
import qualified Ouroboros.Network.AnchoredSeq as AS
import           Ouroboros.Network.Block (HeaderHash, Point (..), SlotNo (..),
                     StandardHash, castPoint, pattern GenesisPoint)
import qualified Ouroboros.Network.Point as Point
import           Test.Ouroboros.Storage.LedgerDB.OrphanArbitrary ()
import           Test.QuickCheck
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.QuickCheck (testProperty)
import           Text.Show.Pretty (ppShow)



tests :: TestTree
tests = testGroup "Ledger" [ testGroup "DbChangelog"
      [ testProperty "empty changelog satisfies invariants"
        prop_emptySatisfiesInvariants
      , testProperty "constructor generated changelog satisfies invariants"
        prop_generatedSatisfiesInvariants
      , testProperty "flushing keeps invariants"
        prop_flushDbChangelogKeepsInvariants
      , testProperty "rolling back keeps invariants"
        prop_rollbackDbChangelogKeepsInvariants
      , testProperty "prefixing back to anchor keeps invariants"
        prop_prefixBackToAnchorKeepsInvariants
      , testProperty "flushing keeps immutable tip"
        prop_flushingKeepsImmutableTip
      , testProperty "extending adds head to volatile states"
        prop_extendingAdvancesTipOfVolatileStates
      , testProperty "rollback after extension is noop"
        prop_rollbackAfterExtendIsNoop
      , testProperty "pruning leaves at most maxRollback volatile states"
        prop_pruningLeavesAtMostMaxRollbacksVolatileStates
      , testProperty "flushing splits immutable and volatile"
        prop_flushingSplitsImmutableAndVolatile
      , testProperty "prefixing back to anchor is rolling back volatile states"
        prop_prefixBackToAnchorIsRollingBackVolatileStates
      , testProperty "prefix back to volatile tip is a noop"
        prop_rollBackToVolatileTipIsNoop
      ]
  ]

{-------------------------------------------------------------------------------
  Test setup
-------------------------------------------------------------------------------}

data DbChangelogTestSetup = DbChangelogTestSetup
  { operations          :: [Operation TestLedger]
  , originalDbChangelog :: DbChangelog TestLedger
  }

data DbChangelogTestSetupWithRollbacks = DbChangelogTestSetupWithRollbacks
  { testSetup :: DbChangelogTestSetup
  , rollbacks :: Int
  } deriving (Show)

instance Show DbChangelogTestSetup where
  show = ppShow . operations

instance Arbitrary DbChangelogTestSetup where

  arbitrary = sized $ \n -> do
    slotNo <- oneof [pure Origin, At <$> SlotNo <$> chooseEnum (1, 1000)]
    operations <- genOperations slotNo n
    pure $ DbChangelogTestSetup
      { operations = operations
      , originalDbChangelog = emptyDbChangelogAtSlot slotNo
      }

  shrink dblog = takeWhileJust $ tail (iterate reduce (Just dblog))
    where
      reduce (Just (DbChangelogTestSetup (_:ops) dblog')) = Just $ DbChangelogTestSetup ops dblog'
      reduce _ = Nothing
      takeWhileJust = catMaybes . takeWhile isJust

instance Arbitrary DbChangelogTestSetupWithRollbacks where
  arbitrary = do
    setup <- arbitrary
    let dblog = resultingDbChangelog setup
    rollbacks <- chooseInt (0, AS.length (changelogVolatileStates dblog))
    pure $ DbChangelogTestSetupWithRollbacks
      { testSetup = setup
      , rollbacks = rollbacks
      }

emptyDbChangelogAtSlot :: WithOrigin SlotNo -> DbChangelog TestLedger
emptyDbChangelogAtSlot slotNo = emptyDbChangeLog (TestLedger ApplyEmptyMK $ pointAtSlot slotNo)

resultingDbChangelog :: DbChangelogTestSetup -> DbChangelog TestLedger
resultingDbChangelog setup = applyOperations (operations setup) (originalDbChangelog setup)

applyOperations :: (TableStuff l, GetTip (l EmptyMK))
  => [Operation l] -> DbChangelog l -> DbChangelog l
applyOperations ops dblog = foldr' apply' dblog ops
  where apply' (Extend newState) dblog' = extendDbChangelog dblog' newState
        apply' (Prune sp) dblog'        = pruneVolatilePartDbChangelog sp dblog'


{-------------------------------------------------------------------------------
  Invariants
-------------------------------------------------------------------------------}

volatileTipAnchorsImmutable :: (GetTip (l EmptyMK), Eq (l EmptyMK)) => DbChangelog l -> Bool
volatileTipAnchorsImmutable DbChangelog { changelogImmutableStates, changelogVolatileStates } =
  AS.anchor changelogVolatileStates == AS.headAnchor changelogImmutableStates

immutableAnchored :: DbChangelog TestLedger -> Bool
immutableAnchored DbChangelog { changelogDiffAnchor, changelogImmutableStates } =
  changelogDiffAnchor == fmap Point.blockPointSlot point
  where point = getPoint $ getTip $ unDbChangelogState $ AS.anchor $ changelogImmutableStates

sameNumberOfDiffsAsStates :: DbChangelog TestLedger -> Bool
sameNumberOfDiffsAsStates dblog = AS.length imm + AS.length vol == lengthSeqUtxoDiff diffs
  where imm = changelogImmutableStates dblog
        vol = changelogVolatileStates dblog
        ApplySeqDiffMK diffs = unTestTables $ changelogDiffs dblog

checkInvariants :: DbChangelog TestLedger -> Bool
checkInvariants dblog = volatileTipAnchorsImmutable dblog &&
                        immutableAnchored dblog &&
                        sameNumberOfDiffsAsStates dblog


{-------------------------------------------------------------------------------
  Properties
-------------------------------------------------------------------------------}

prop_emptySatisfiesInvariants :: Property
prop_emptySatisfiesInvariants =
  property $ checkInvariants (emptyDbChangelogAtSlot Origin)

prop_generatedSatisfiesInvariants :: DbChangelogTestSetup -> Property
prop_generatedSatisfiesInvariants setup =
  property $ checkInvariants (resultingDbChangelog setup)

prop_flushingKeepsImmutableTip :: DbChangelogTestSetup -> Property
prop_flushingKeepsImmutableTip setup =
  property $ (toKeepTip == toFlushTip) && (toFlushTip == dblogTip)
  where
    dblog = resultingDbChangelog setup
    (toFlush, toKeep) = flushDbChangelog DbChangelogFlushAllImmutable dblog
    dblogTip = youngestImmutableSlotDbChangelog dblog
    toFlushTip = youngestImmutableSlotDbChangelog toFlush
    toKeepTip = youngestImmutableSlotDbChangelog toKeep

prop_extendingAdvancesTipOfVolatileStates :: DbChangelogTestSetup -> Property
prop_extendingAdvancesTipOfVolatileStates setup =
  property $ (tlTip state) == (tlTip new)
  where
    dblog = resultingDbChangelog setup
    state = nextState dblog
    dblog' = extendDbChangelog dblog state
    new = unDbChangelogState $ either id id $ AS.head (changelogVolatileStates dblog')

prop_rollbackAfterExtendIsNoop :: DbChangelogTestSetup -> Positive Int -> Property
prop_rollbackAfterExtendIsNoop setup (Positive n) =
  property (dblog == rollbackDbChangelog n (nExtensions n dblog))
  where
    dblog = resultingDbChangelog setup

prop_pruningLeavesAtMostMaxRollbacksVolatileStates ::
  DbChangelogTestSetup -> SecurityParam -> Property
prop_pruningLeavesAtMostMaxRollbacksVolatileStates setup sp@(SecurityParam maxRollbacks) =
  property $ AS.length (changelogVolatileStates dblog') <= fromIntegral maxRollbacks
  where
    dblog = resultingDbChangelog setup
    dblog' = pruneVolatilePartDbChangelog sp dblog

prop_flushingSplitsImmutableAndVolatile :: DbChangelogTestSetup -> Property
prop_flushingSplitsImmutableAndVolatile setup =
  property $ AS.length (changelogVolatileStates toFlush) == 0 &&
             AS.length (changelogImmutableStates toKeep) == 0 &&
             diffSeqDblog == diffSeqJoined
  where
    dblog = resultingDbChangelog setup
    (toFlush, toKeep) = flushDbChangelog DbChangelogFlushAllImmutable dblog
    (ApplySeqDiffMK diffSeqToFlush) = unTestTables $ changelogDiffs toFlush
    (ApplySeqDiffMK diffSeqToKeep) = unTestTables $ changelogDiffs toKeep
    diffSeqJoined = unsafeJoinSeqUtxoDiffs diffSeqToFlush diffSeqToKeep
    (ApplySeqDiffMK diffSeqDblog) = unTestTables $ changelogDiffs dblog

prop_prefixBackToAnchorKeepsInvariants :: DbChangelogTestSetup -> Property
prop_prefixBackToAnchorKeepsInvariants setup = property $ checkInvariants dblog
  where
    dblog = prefixBackToAnchorDbChangelog $ resultingDbChangelog setup

prop_flushDbChangelogKeepsInvariants :: DbChangelogTestSetup -> Property
prop_flushDbChangelogKeepsInvariants setup =
  property $ checkInvariants toFlush && checkInvariants toKeep
  where
    (toFlush, toKeep) = flushDbChangelog DbChangelogFlushAllImmutable $
      resultingDbChangelog setup

-- TODO: This fails due to rollbackDbChangelog being partial. We need n to be at most
-- the length of the changelog (or maybe the volatile part of it).
prop_rollbackDbChangelogKeepsInvariants ::
  DbChangelogTestSetupWithRollbacks -> Property
prop_rollbackDbChangelogKeepsInvariants setup = property $ checkInvariants dblog
  where
    n = rollbacks setup
    dblog = rollbackDbChangelog n (resultingDbChangelog $ testSetup setup)


prop_prefixBackToAnchorIsRollingBackVolatileStates :: DbChangelogTestSetup -> Property
prop_prefixBackToAnchorIsRollingBackVolatileStates setup =
  property $ rolledBack == toAnchor
  where
    dblog = resultingDbChangelog setup
    n = AS.length (changelogVolatileStates dblog)
    rolledBack = rollbackDbChangelog n dblog
    toAnchor = prefixBackToAnchorDbChangelog dblog

prop_rollBackToVolatileTipIsNoop ::
  Positive Int -> DbChangelogTestSetup -> Property
prop_rollBackToVolatileTipIsNoop (Positive n) setup = property $ Just dblog == dblog'
  where
    dblog = resultingDbChangelog setup
    pt = getTip $ unDbChangelogState $ AS.headAnchor $ changelogVolatileStates dblog
    dblog' = prefixDbChangelog pt $ nExtensions n dblog

unsafeJoinSeqUtxoDiffs :: Ord k => SeqUtxoDiff k v -> SeqUtxoDiff k v -> SeqUtxoDiff k v
unsafeJoinSeqUtxoDiffs (SeqUtxoDiff ft1) (SeqUtxoDiff ft2) =
  SeqUtxoDiff (ft1 FT.>< ft2)

{-------------------------------------------------------------------------------
  Generators
-------------------------------------------------------------------------------}

data Operation l = Extend (l DiffMK) | Prune SecurityParam
deriving instance Show (l DiffMK) => Show (Operation l)

pointAtSlot :: WithOrigin SlotNo -> Point (TestLedger EmptyMK)
pointAtSlot = Point.withOrigin GenesisPoint (\slotNo -> Point $ At $ Point.Block slotNo H)

type Key = String

data GenOperationsState = GenOperationsState {
    osSlotNo            :: !(WithOrigin SlotNo)
  , osOps               :: ![Operation TestLedger]
  , osActiveUtxos       :: !(Map Key Int)
  , osPendingInsertions :: !(Map Key Int)
  , osConsumedUtxos     :: !(Set Key)
  } deriving (Show)

applyPending :: GenOperationsState -> GenOperationsState
applyPending gosState = gosState
  { osActiveUtxos = Map.union (osActiveUtxos gosState) (osPendingInsertions gosState)
  , osPendingInsertions = Map.empty
  }


genOperations :: WithOrigin SlotNo -> Int -> Gen [Operation TestLedger]
genOperations slotNo n = osOps <$> genOperations' slotNo n

genOperations' :: WithOrigin SlotNo -> Int -> Gen GenOperationsState
genOperations' slotNo nOps = execStateT (replicateM_ nOps genOperation) initState
  where
    initState = GenOperationsState {
        osSlotNo = slotNo
      , osActiveUtxos = Map.empty
      , osPendingInsertions = Map.empty
      , osConsumedUtxos = Set.empty
      , osOps = []
      }

    genOperation = do
      op <- frequency' [ (1, genPrune), (10, genExtend) ]
      modify' $ \st -> st { osOps = op:osOps st }

    genPrune = Prune <$> SecurityParam <$> lift (chooseEnum (1, 10))

    genExtend = do
      nextSlotNo <- advanceSlotNo =<< (lift $ chooseEnum (1, 5))
      diff <- genUtxoDiff
      pure $ Extend $ TestLedger (ApplyDiffMK diff) (castPoint $ pointAtSlot nextSlotNo)

    advanceSlotNo by = do
      nextSlotNo <- gets (At . Point.withOrigin by (+ by) . osSlotNo)
      modify' $ \st -> st { osSlotNo = nextSlotNo }
      pure nextSlotNo

    genUtxoDiff = do
      nEntries <- lift $ chooseInt (1, 10)
      entries <- replicateM nEntries genUtxoDiffEntry
      modify' applyPending
      pure $ UtxoDiff $ Map.fromList entries

    genUtxoDiffEntry = do
      activeUtxos <- gets osActiveUtxos
      consumedUtxos <- gets osConsumedUtxos
      oneof' $ catMaybes [
        genDelEntry activeUtxos,
        genInsertEntry consumedUtxos]

    genDelEntry activeUtxos =
      if Map.null activeUtxos then Nothing
      else Just $ do
        (k, v) <- lift $ elements (Map.toList activeUtxos)
        modify' $ \st -> st
          { osActiveUtxos = Map.delete k (osActiveUtxos st)
          }
        pure (k, UtxoEntryDiff v UedsDel)

    genInsertEntry consumedUtxos = Just $ do
      k <- lift $ genKey `suchThat` (\a -> Set.notMember a consumedUtxos)
      v <- lift $ arbitrary
      modify' $ \st -> st
        { osPendingInsertions = Map.insert k v (osPendingInsertions st)
        , osConsumedUtxos = Set.insert k (osConsumedUtxos st)
        }
      pure (k, UtxoEntryDiff v UedsIns)

oneof' :: [StateT s Gen a] -> StateT s Gen a
oneof' [] = error "QuickCheck.oneof used with empty list"
oneof' gs = lift (chooseInt (0,length gs - 1)) >>= (gs !!)

frequency' :: [(Int, StateT s Gen a)] -> StateT s Gen a
frequency' [] = error "QuickCheck.frequency used with empty list"
frequency' xs
  | any (< 0) (map fst xs) =
    error "QuickCheck.frequency: negative weight"
  | all (== 0) (map fst xs) =
    error "QuickCheck.frequency: all weights were zero"
frequency' xs0 = lift (chooseInt (1, tot)) >>= (`pick` xs0)
  where
    tot = sum (map fst xs0)

    pick n ((k,x):xs)
        | n <= k    = x
        | otherwise = pick (n-k) xs
    pick _ _  = error "QuickCheck.pick used with empty list"

genKey :: Gen Key
genKey = replicateM 2 $ elements ['A'..'Z']


{-------------------------------------------------------------------------------
  Generators
-------------------------------------------------------------------------------}

data TestLedger (mk :: MapKind) = TestLedger {
  tlUtxos :: ApplyMapKind mk Key Int,
  tlTip   :: Point (TestLedger EmptyMK)
}

nextState :: (DbChangelog TestLedger) -> TestLedger DiffMK
nextState dblog = TestLedger
            { tlTip = pointAtSlot $ nextSlot (getTipSlot old)
            , tlUtxos = ApplyDiffMK $ emptyUtxoDiff
            }
  where
    old = unDbChangelogState $ either id id $ AS.head (changelogVolatileStates dblog)
    nextSlot Origin = At 1
    nextSlot (At x) = At (x + 1)

nExtensions :: Int -> DbChangelog TestLedger -> DbChangelog TestLedger
nExtensions n dblog = (iterate extend dblog) !! n
  where extend dblog' = extendDbChangelog dblog' (nextState dblog')

deriving instance Show (TestLedger EmptyMK)
deriving instance Show (TestLedger DiffMK)

instance GetTip (TestLedger EmptyMK) where
  getTip = tlTip

instance GetTip (TestLedger DiffMK) where
  getTip = castPoint . tlTip

data H = H deriving (Eq, Ord, Show, Generic)
deriving anyclass instance NoThunks H
type instance HeaderHash (TestLedger mk) = H

instance StandardHash (TestLedger EmptyMK)

deriving instance Eq (TestLedger EmptyMK)
deriving instance Eq (LedgerTables TestLedger DiffMK)
deriving instance Eq (LedgerTables TestLedger ValuesMK)

instance ShowLedgerState (LedgerTables TestLedger) where
  showsLedgerState _ (TestTables t) = showString "TestTables " . shows t

-- REVIEW: What to do with this orphan instance?
instance Show (ApplyMapKind' mk' Key Int) where
  show ap = showsApplyMapKind ap ""

-- TODO: Make this more useful
instance ShowLedgerState TestLedger where
  showsLedgerState _ (TestLedger _ _) = showString "TestLedger"

instance TableStuff TestLedger where
  data LedgerTables TestLedger mk = TestTables { unTestTables :: ApplyMapKind mk Key Int }
  projectLedgerTables = TestTables . tlUtxos
  withLedgerTables st (TestTables x) = st { tlUtxos = x }
  pureLedgerTables = TestTables
  mapLedgerTables f (TestTables x) = TestTables (f x)
  traverseLedgerTables f (TestTables x) = TestTables <$> f x
  zipLedgerTables f (TestTables x) (TestTables y) = TestTables (f x y)
  zipLedgerTables2 f (TestTables x) (TestTables y) (TestTables z) = TestTables (f x y z)
  zipLedgerTablesA f (TestTables x) (TestTables y) = TestTables <$> f x y
  zipLedgerTables2A f (TestTables x) (TestTables y) (TestTables z) = TestTables <$> f x y z
  foldLedgerTables f (TestTables x) = f x
  foldLedgerTables2 f (TestTables x) (TestTables y) = f x y
  namesLedgerTables = TestTables $ NameMK "TestTables"

deriving instance Eq (LedgerTables TestLedger SeqDiffMK)

-- | Scratch

run :: IO ()
run = do
  setup <- (generate arbitrary :: IO (DbChangelogTestSetup))
  print setup

