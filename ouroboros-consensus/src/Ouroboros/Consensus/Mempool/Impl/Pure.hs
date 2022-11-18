{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Pure side of the Mempool implementation.
--
-- Operations are performed in a pure style returning data types that model
-- the control flow through the operation and can then be interpreted to perform
-- the actual STM/IO operations.

module Ouroboros.Consensus.Mempool.Impl.Pure (
    -- * Mempool
    TransactionProcessed (..)
  , pureGetSnapshotFor
  , pureRemoveTxs
  , pureSyncWithLedger
  , pureTryAddTxs
    -- * MempoolSnapshot
  , implSnapshotFromIS
  ) where

import           Control.Exception (assert)
import qualified Data.List.NonEmpty as NE
import           Data.Maybe (isJust, isNothing)
import qualified Data.Set as Set

import           Ouroboros.Network.Block

import           Ouroboros.Consensus.Ledger.Abstract
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Mempool.Impl.Types
import           Ouroboros.Consensus.Mempool.TxSeq (TicketNo, TxTicket (..),
                     zeroTicketNo)
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq

import           Ouroboros.Network.Protocol.TxSubmission2.Type (TxSizeInBytes)

{-------------------------------------------------------------------------------
  Mempool Implementation
-------------------------------------------------------------------------------}

-- | Result of processing a transaction to be added to the mempool.
data TransactionProcessed blk =
  TransactionProcessed
    (Maybe (InternalState blk))
    -- ^ If the transaction was accepted, the new state that can be written to
    -- the TVar.
    (MempoolAddTxResult blk)
    -- ^ The result of trying to add the transaction to the mempool.
    (TraceEventMempool blk)
    -- ^ The event emitted by the operation.

-- | Craft a 'TryAddTxs' value containing the resulting state if applicable, the
-- tracing event and the result of adding this transaction. See the
-- documentation of 'implTryAddTxs' for some more context.
pureTryAddTxs
  :: ( LedgerSupportsMempool blk
     , HasTxId (GenTx blk)
     )
  => LedgerCfg (LedgerState blk)
     -- ^ The ledger configuration.
  -> (GenTx blk -> TxSizeInBytes)
     -- ^ The function to calculate the size of a transaction.
  -> WhetherToIntervene
  -> GenTx blk
     -- ^ The transaction to add to the mempool.
  -> InternalState blk
     -- ^ The current internal state of the mempool.
  -> LedgerTables (LedgerState blk) ValuesMK
     -- ^ Values for this transaction
  -> Maybe (TransactionProcessed blk)
pureTryAddTxs cfg txSize wti tx is values
  | let size    = txSize tx
        curSize = msNumBytes  $ isMempoolSize is
  , curSize + size > getMempoolCapacityBytes (isCapacity is)
  = Nothing
  | otherwise
  = Just $ case eVtx of
      -- We only extended the ValidationResult with a single transaction
      -- ('tx'). So if it's not in 'vrInvalid', it must be in 'vrNewValid'.
      Right vtx ->
        assert (isJust (vrNewValid vr)) $
          TransactionProcessed
            (Just is')
            (MempoolTxAdded vtx)
            (TraceMempoolAddedTx
              vtx
              (isMempoolSize is)
              (isMempoolSize is')
            )
      Left err ->
        assert (isNothing (vrNewValid vr))  $
          assert (length (vrInvalid vr) == 1) $
            TransactionProcessed
              Nothing
              (MempoolTxRejected tx err)
              (TraceMempoolRejectedTx
               tx
               err
               (isMempoolSize is)
              )
    where
      (eVtx, vr) = extendVRNew cfg txSize wti tx $ validationResultFromIS values is
      is'        = internalStateFromVR vr

-- | Craft a 'RemoveTxs' that manually removes the given transactions from the
-- mempool, returning inside it an updated InternalState.
pureRemoveTxs
  :: ( LedgerSupportsMempool blk
     , HasTxId (GenTx blk)
     )
  => MempoolCapacityBytesOverride
  -> LedgerConfig blk
  -> SlotNo
  -> TickedLedgerState blk DiffMK
  -> LedgerTables (LedgerState blk) ValuesMK
  -> TicketNo
  -> [TxTicket (Validated (GenTx blk))] -- ^ Txs to keep
  -> NE.NonEmpty (GenTxId blk) -- ^ IDs to remove
  -> (InternalState blk, TraceEventMempool blk)
pureRemoveTxs capacityOverride lcfg slot lstate values tkt txs txIds=
    let (is', removed) = revalidate
                           capacityOverride
                           lcfg
                           slot
                           lstate
                           values
                           tkt
                           txs
        trace = TraceMempoolManuallyRemovedTxs
                  txIds
                  removed
                  (isMempoolSize is')
    in (is', trace)

revalidate ::
  ( LedgerSupportsMempool blk
  , HasTxId (GenTx blk)
  )
  => MempoolCapacityBytesOverride
  -> LedgerCfg (LedgerState blk)
  -> SlotNo
  -> TickedLedgerState blk DiffMK
  -> LedgerTables (LedgerState blk) ValuesMK -- ^ Values for all the txs to revalidate
  -> TicketNo
  -> [TxTicket (Validated (GenTx blk))] -- ^ Txs to revalidate
  -> ( InternalState blk
     , [Validated (GenTx blk)]
     )  -- ^ Resulting state and new invalid transactions
revalidate capacityOverride lcfg slot lstate values tkt txs =
  let vr = revalidateTxsFor
             capacityOverride
             lcfg
             slot
             lstate
             values
             tkt
             txs
  in (internalStateFromVR vr, map fst (vrInvalid vr))

-- | Create a 'SyncWithLedger' value representing the values that will need to
-- be stored for committing this synchronization with the Ledger.
pureSyncWithLedger
  :: (LedgerSupportsMempool blk, HasTxId (GenTx blk))
  => MempoolCapacityBytesOverride
  -> LedgerConfig blk
  -> SlotNo
  -> TickedLedgerState blk DiffMK
  -> LedgerTables (LedgerState blk) ValuesMK
  -> InternalState blk
  -> ( InternalState blk
     , MempoolSnapshot blk
     , Maybe (TraceEventMempool blk)
     )
pureSyncWithLedger capacityOverride lcfg slot lstate values istate =
    let (is', removed) = revalidate
                           capacityOverride
                           lcfg
                           slot
                           lstate
                           values
                           (isLastTicketNo istate)
                           (TxSeq.toList $ isTxs istate)
        mTrace         = if null removed
                         then
                           Nothing
                         else
                           Just $ TraceMempoolRemoveTxs removed (isMempoolSize is')
    in
      (is', implSnapshotFromIS is', mTrace)

-- | Get a snapshot of the mempool state that is valid with respect to
-- the given ledger state, together with the ticked ledger state.
pureGetSnapshotFor
  :: forall blk.
     ( LedgerSupportsMempool blk
     , HasTxId (GenTx blk)
     )
  => MempoolCapacityBytesOverride
  -> LedgerConfig blk
  -> LedgerTables (LedgerState blk) ValuesMK
  -> InternalState blk
  -> ForgeLedgerState blk
  -> MempoolSnapshot blk
pureGetSnapshotFor _ _ _ _ ForgeInUnknownSlot{} = error "Tried to get a snapshot for unknown slot"
pureGetSnapshotFor capacityOverride cfg values is (ForgeInKnownSlot slot st) = implSnapshotFromIS $
  if (pointHash (isTip is) == castHash (getTipHash st) && isSlotNo is == slot)
  then is
  else fst $ revalidate
               capacityOverride
               cfg
               slot
               st
               values
               (isLastTicketNo is)
               (TxSeq.toList $ isTxs is)

{-------------------------------------------------------------------------------
  MempoolSnapshot Implementation
-------------------------------------------------------------------------------}

-- | Create a 'MempoolSnapshot' from a given 'InternalState' of the mempool.
implSnapshotFromIS
  :: HasTxId (GenTx blk)
  => InternalState blk
  -> MempoolSnapshot blk
implSnapshotFromIS is = MempoolSnapshot {
      snapshotTxs         = implSnapshotGetTxs         is
    , snapshotTxsAfter    = implSnapshotGetTxsAfter    is
    , snapshotLookupTx    = implSnapshotGetTx          is
    , snapshotHasTx       = implSnapshotHasTx          is
    , snapshotMempoolSize = implSnapshotGetMempoolSize is
    , snapshotSlotNo      = isSlotNo                   is
    , snapshotTipHash     = pointHash (isTip                      is)
    }
 where
  implSnapshotGetTxs :: InternalState blk
                     -> [(Validated (GenTx blk), TicketNo)]
  implSnapshotGetTxs = flip implSnapshotGetTxsAfter zeroTicketNo

  implSnapshotGetTxsAfter :: InternalState blk
                          -> TicketNo
                          -> [(Validated (GenTx blk), TicketNo)]
  implSnapshotGetTxsAfter IS{isTxs} =
    TxSeq.toTuples . snd . TxSeq.splitAfterTicketNo isTxs

  implSnapshotGetTx :: InternalState blk
                    -> TicketNo
                    -> Maybe (Validated (GenTx blk))
  implSnapshotGetTx IS{isTxs} = (isTxs `TxSeq.lookupByTicketNo`)

  implSnapshotHasTx :: Ord (GenTxId blk)
                    => InternalState blk
                    -> GenTxId blk
                    -> Bool
  implSnapshotHasTx IS{isTxIds} = flip Set.member isTxIds

  implSnapshotGetMempoolSize :: InternalState blk
                             -> MempoolSize
  implSnapshotGetMempoolSize = TxSeq.toMempoolSize . isTxs
