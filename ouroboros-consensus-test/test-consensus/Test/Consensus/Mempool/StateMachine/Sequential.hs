{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE BangPatterns #-}
-- |

module Test.Consensus.Mempool.StateMachine.Sequential where

import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Reader
import           Control.Tracer
import           Data.Coerce
import           Data.Foldable
import           Data.IORef
import           Data.Kind
import           Data.List (intercalate)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import           Data.Map.Diff.Strict (applyDiff)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromJust)
import qualified Data.Set as Set
import           Data.TreeDiff (genericToExpr, Expr (..))
import           Data.TreeDiff.OMap (fromList)
import           GHC.Generics
import           Text.Layout.Table

import           Cardano.Slotting.Slot
import           Cardano.Slotting.Time (slotLengthFromSec)

import           Ouroboros.Consensus.Block (pointSlot)
import           Ouroboros.Consensus.HardFork.History.EraParams
import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.Extended
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Mempool
import           Ouroboros.Consensus.Mempool.Impl.Types (InternalState (..))
import           Ouroboros.Consensus.Mempool.TxSeq (TxSeq)
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq
import           Ouroboros.Consensus.Protocol.Abstract
import           Ouroboros.Consensus.Storage.LedgerDB.HD.BackingStore
import           Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq (cumulativeDiff)
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq as DS
import           Ouroboros.Consensus.Storage.LedgerDB.OnDisk hiding (flush)
import           Ouroboros.Consensus.Util
import           Ouroboros.Consensus.Util.IOLike
import qualified Ouroboros.Consensus.Util.MonadSTM.RAWLock as RAWLock

import           Test.Util.TestBlock hiding (TestBlock)

import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.QuickCheck.Random (QCGen)
import           Test.StateMachine
import           Test.StateMachine.DotDrawing (GraphOptions(GraphOptions), GraphvizOutput (..))
import           Test.StateMachine.Types (runGenSym, newCounter, Pair (..), ParallelCommandsF (..), Command (..), Commands (..))
import qualified Test.StateMachine.Types.Rank2 as Rank2

import           Test.Consensus.Mempool.Block

import qualified Debug.Trace as Debug

{-------------------------------------------------------------------------------
  Action
-------------------------------------------------------------------------------}
-- | The actions that we will consider for the mempool are only the ones that
-- alter the mempool.
type Action :: Type -> (Type -> Type) -> Type
data Action blk r
    -- | System is booted up with this state
  = Init !(TickedLedgerState blk ValuesMK)

    -- | Try to add the given transactions to the mempool
  | TryAddTx  !(GenTx blk)

    -- | Perform a sync with the ledger DB
  | SyncLedger

    -- | Make the ledger db go out of sync with the mempool by giving a new fork.
    --
    -- The fork *MUST* have the current immutable chain as a prefix.
    --
    -- This means @switchToFork@
  | Switch !(NE.NonEmpty (LedgerState blk ValuesMK))

    -- | Flush one state to the disk if possible
  | Flush

  deriving stock Generic1
  deriving anyclass (Rank2.Functor, Rank2.Foldable, Rank2.Traversable)

instance CommandNames (Action blk) where
  cmdName Init{}       = "Init"
  cmdName TryAddTx{}   = "TryAddTx"
  cmdName SyncLedger{} = "SyncLedger"
  cmdName Switch{}     = "Switch"
  cmdName Flush{}      = "Flush"

  cmdNames _ = [ "Init"
               , "TryAddTx"
               , "SyncLedger"
               , "Switch"
               , "Flush"
               ]

instance ( Show (TickedLedgerState blk ValuesMK)
         , Show (LedgerState blk ValuesMK)
         , Show (GenTx blk)
         , Show (MempoolChangelog blk)
         ) => Show (Action blk r) where
  show = \case
    Init ls          -> "Init " <> show ls
    TryAddTx gts     -> "TryAddTx " <> show gts
    SyncLedger       -> "SyncLedger"
    Flush            -> "Flush"
    Switch sts       -> "Switch to ["
                        <> (\ne -> show (length ne - 1)
                                                  <> " states, "
                                                  <> show (NE.last ne))
                           sts
                        <> "] "

{-------------------------------------------------------------------------------
  Response
-------------------------------------------------------------------------------}

-- | Responses that the system can give
type Response :: Type -> (Type -> Type) -> Type
data Response blk r
 =
    ResponseOk

  | RespTryAddTx
    (Maybe (MempoolAddTxResult blk)) -- ^ Result of adding the transaction
    (TickedLedgerState blk ValuesMK) -- ^ Ledger state on top of which the transaction was processed (works only for sequential case)

  | SwitchedTo
     (NonEmpty (LedgerState blk ValuesMK)) -- ^ The new sequence [anchor..tip]

  | Flushed
     (LedgerState blk ValuesMK) -- ^ The state that is the new tip

  deriving stock (Generic1)
  deriving anyclass Rank2.Foldable

instance ( Show (Validated (GenTx blk))
         , Show (ApplyTxErr blk)
         , Show (GenTx blk)
         , Show (TickedLedgerState blk ValuesMK)
         , Show (LedgerState blk ValuesMK)
         ) => Show (Response blk r) where
  show ResponseOk = "ResponseOk"
  show (RespTryAddTx processed st) = "RespTryAdd " <> show processed <> " onto " <> show st
  show (SwitchedTo sts) = "SwitchedTo " <> show (NE.take 2 sts) <> " to " <> show (NE.last sts)
  show (Flushed st) = "Flushed, new state = " <> show st

deriving instance ( Eq (LedgerState blk ValuesMK)
                  , Eq (TickedLedgerState blk ValuesMK)
                  , Eq (MempoolAddTxResult blk)
                  ) => Eq (Response blk r)

{-------------------------------------------------------------------------------
  Model
-------------------------------------------------------------------------------}

data SeqModel blk r = NeedsInit | Model !(SeqModel' blk)
  deriving Generic

deriving instance Eq (SeqModel' blk) => Eq (SeqModel blk r)
deriving instance Show (SeqModel' blk) => Show (SeqModel blk r)

{-|

The model that will be used in the test. It can be seen in this diagram:

            modelStates
    /----------------------------\

           mempoolAnchor
                v ldbAnchor
                  v
    I-----------M-A--------------- V modelNextTip
                   \-----------------

                  \-----------------/
                     anchorToTip

    \--------------------------------/
            modelNextSync
-}
data SeqModel' blk = SeqModel {
    modelStates          :: !(NonEmpty (LedgerState blk ValuesMK))
  , modelNextSync        :: !(Maybe (NonEmpty (LedgerState blk ValuesMK)))
  , modelTip             :: !(TickedLedgerState blk ValuesMK)
  , modelAnchorsDistance :: !Int
  , modelAnchorToTip     :: !Int
  , modelTxs             :: !(TxSeq (Validated (GenTx blk)))
  , modelNextTicket      :: !TicketNo
  }
  deriving Generic

deriving instance ( Eq (TickedLedgerState blk ValuesMK)
                  , Eq (LedgerState blk ValuesMK)
                  , Eq (TxSeq (Validated (GenTx blk)))
                  ) => Eq (SeqModel' blk)
deriving instance ( Show (TickedLedgerState blk ValuesMK)
                  , Show (LedgerState blk ValuesMK)
                  , Show (TxSeq (Validated (GenTx blk)))
                  ) => Show (SeqModel' blk)

instance ToExpr (TickedLedgerState TestBlock ValuesMK) where
  toExpr = genericToExpr

instance ToExpr TicketNo where
  toExpr (TxSeq.TicketNo t) = App "TicketNo" [ toExpr t ]

instance ToExpr (GenTx TestBlock) where
  toExpr (TestGenTx t _) = genericToExpr t

-- TODO @js: I'm just printing stuff I think is interesting, to not overload the
-- output
instance ToExpr (SeqModel' TestBlock) where
  toExpr SeqModel{..} =
    Rec "SeqModel"
    $ fromList [ ("distanceToTip", toExpr modelAnchorToTip)
               , ("distanceBetweenAnchors", toExpr modelAnchorsDistance)
               , ("modelTip", Lst [toExpr (pointSlot $ getTip modelTip), toExpr (payloadDependentState $ getTickedTestLedger modelTip)])
               , ("modelTxs", toExpr $ map (txForgetValidated . TxSeq.txTicketTx) $ TxSeq.toList modelTxs)
               ]

instance ToExpr (SeqModel TestBlock Concrete)

initModel :: SeqModel blk r
initModel = NeedsInit

{-------------------------------------------------------------------------------
  SUT
-------------------------------------------------------------------------------}

-- | A mock LedgerDB that has the bare minimum to fulfill the LedgerInterface
data TestLedgerDB m blk =
  TestLedgerDB
    !(LedgerBackingStore m (ExtLedgerState blk))
    !(StrictTVar m (NonEmpty (LedgerState blk ValuesMK)))

newLedgerInterface :: forall m.
  ( IOLike m
  )
  => TickedLedgerState TestBlock ValuesMK
 -> m ( TestLedgerDB m TestBlock
      , LedgerInterface m TestBlock
      , RAWLock.RAWLock m ()
      )
newLedgerInterface st = do
  bkst   <- createTVarBackingStore (pointSlot $ getTip st) (ExtLedgerStateTables $ projectLedgerTablesTicked st)
  ledger <- newTVarIO (getTickedTestLedger st NE.:| [])
  rw <- RAWLock.new ()
  pure $ ( TestLedgerDB bkst ledger
         , LedgerInterface {
               getCurrentLedgerAndChangelog = do
                   states <- readTVar ledger
                   pure
                     $ (forgetLedgerTables $ NE.last states,)
                     $ MempoolChangelog (pointSlot $ getTip $ NE.head states)
                     $ changelogFromStates states
             , getBackingStore              = pure bkst
             , withReadLock                 = \m -> RAWLock.withReadAccess rw (\() -> m)
             }
         , rw
         )

-- | Due to the model working with full UTxOs we need to reconstruct a seqdiff
-- on-the-fly for the SUT. This function does that.
changelogFromStates ::
     NonEmpty (LedgerState TestBlock ValuesMK)
  -> LedgerTables (LedgerState TestBlock) SeqDiffMK
changelogFromStates states =
  let
      projected = [ (slot, projectLedgerTables thisSt)
                  | thisSt <- NE.toList states
                  , let slot = pointSlot $ getTip thisSt
                  , slot >= pointSlot (getTip $ NE.head states)
                  ]
      zipped = (\s -> zip s (tail s)) projected

      ext :: (Ord k, Eq v) => SlotNo -> SeqDiffMK k v -> DiffMK k v -> SeqDiffMK k v
      ext sl (ApplySeqDiffMK sq) (ApplyDiffMK d) = ApplySeqDiffMK $ DS.extend sq sl d

  in foldl'
        (\acc ((_, prev), (thisslot, next)) ->
           zipLedgerTables
             (ext (withOrigin' thisslot))
             acc
             (zipLedgerTables (rawForgetValues .: rawCalculateDifference) prev next)
        )
        polyEmptyLedgerTables
        zipped

semantics ::
     LedgerConfig TestBlock
  -> Action TestBlock Concrete
  -> ReaderT (IORef ( Mempool IO TestBlock
                    , TestLedgerDB IO TestBlock
                    , RAWLock.RAWLock IO ()
                    , StrictTMVar IO (InternalState TestBlock) -- direct access to the internal ledger state
                    )
             )
             IO
             (Response TestBlock Concrete)
semantics cfg action = do
  ref <- ask
  lift $ do
   case action of
    Init st -> do
      Debug.traceM "\n<- Init"
      (testDb, iface, rwl) <- newLedgerInterface st
      (mp, mpenv) <- openMempoolWithoutSyncThread' iface cfg (MempoolCapacityBytesOverride (MempoolCapacityBytes 100)) nullTracer txInBlockSize
      atomicWriteIORef ref (mp, testDb, rwl, mpEnvStateVar mpenv)
      Debug.traceM "-> Init"
      pure ResponseOk

    TryAddTx txs -> do
      Debug.traceM "<- AddTxs"
      (mp, _, _, state) <- readIORef ref
      s <- atomically $ readTMVar state
      (addTxsProcessed_, _) <- tryAddTxs mp DoNotIntervene [txs]
      Debug.traceM "-> AddTxs"
      pure $ RespTryAddTx (fmap NE.head $ NE.nonEmpty addTxsProcessed_) (isLedgerState s `withLedgerTablesTicked` polyEmptyLedgerTables :: TickedLedgerState TestBlock ValuesMK)

    SyncLedger -> do
      Debug.traceM "<- Sync"
      (mp, _, _, _) <- readIORef ref
      !_ <- syncWithLedger mp
      Debug.traceM "-> Sync"
      pure ResponseOk

    Flush -> do
      Debug.traceM "<- Flush"
      (_, TestLedgerDB (LedgerBackingStore bs) stv, rwl, _) <- readIORef ref
      RAWLock.withWriteAccess rwl (\() -> do
        states <- atomically $ readTVar stv
        ((),) <$> case NE.tail states of
          -- if we have more than just one state
          next:more -> do
            -- Write one set of differences
            bsWrite bs (withOrigin' $ pointSlot $ getTip next)
              $ ExtLedgerStateTables
              $ zipLedgerTables
                  (rawForgetValues .: rawCalculateDifference)
                  (projectLedgerTables (NE.head states))
                  (projectLedgerTables next)
            -- advance the ledger db
            atomically $ writeTVar stv (next NE.:| more)
            Debug.traceM "-> Flush"
            pure $ Flushed next
          [] -> Debug.traceM "-> Flush" >> pure ResponseOk
        )

    Switch states -> do
      Debug.traceM "<- Switch"
      (_, TestLedgerDB _ stv, _, _) <- readIORef ref
      SwitchedTo <$> atomically (do
        (anchor NE.:| _) <- readTVar stv
        -- The lists of states are pre-generated so some of them might become
        -- obsolete. That's why we filter out the ones that have became
        -- obsolete. Also we luckily can rearrange the blocks without breaking
        -- invariants (is this true? won't utxhist become out of sync?).
        let sts' = anchor NE.:| NE.filter (\ls -> pointSlot (getTip ls) > pointSlot (getTip anchor)) states
        writeTVar stv sts'
        Debug.traceM "-> Switch"
        pure sts')

{-------------------------------------------------------------------------------
  Transition
-------------------------------------------------------------------------------}

syncLedger :: EraParams -> SeqModel TestBlock r -> SeqModel TestBlock r
syncLedger _ NeedsInit = error "transitions: model needs init"
syncLedger cfg m@(Model SeqModel{..}) =
  case modelNextSync of
    Nothing -> m
    Just sy ->
      Model $ SeqModel {
            modelAnchorToTip
          , modelAnchorsDistance = 0
          , modelNextSync        = Nothing
          , modelNextTicket
          , modelStates          = maybe modelStates id modelNextSync
          , modelTip             = foldl (\s t -> apply (txForgetValidated t) s) (tick cfg . NE.last $ sy) modelTxs
          , modelTxs             = fst $ foldApplyTxs cfg sy (TxSeq.toList modelTxs)
          }

tryAddTx :: GenTx TestBlock -> SeqModel TestBlock r -> SeqModel TestBlock r
tryAddTx _ NeedsInit = error "transitions: model needs init"
tryAddTx tx@(TestGenTx t i) m@(Model SeqModel{..}) = case validate tx modelTip of
  Right () ->
    Model $ SeqModel {
            modelAnchorToTip
          , modelAnchorsDistance
          , modelNextSync
          , modelNextTicket      = succ modelNextTicket
          , modelStates
          , modelTip             = apply tx modelTip
          , modelTxs             = modelTxs TxSeq.:> (TxSeq.TxTicket (TestValidatedTx t i) modelNextTicket 1)
          }
  _ -> m

flush :: SeqModel blk r -> SeqModel blk r
flush NeedsInit = error "transitions: model needs init"
flush (Model SeqModel{..}) = Model $ SeqModel {
            modelAnchorToTip     = modelAnchorToTip - 1
          , modelAnchorsDistance = modelAnchorsDistance + 1
          , modelNextSync        = Just $ maybe modelStates id modelNextSync
          , modelNextTicket
          , modelStates
          , modelTip
          , modelTxs
          }

switch :: Eq (LedgerState blk ValuesMK)
  => NonEmpty (LedgerState blk ValuesMK)
  -> SeqModel blk r
  -> SeqModel blk r
switch _ NeedsInit = error "transitions: model needs init"
switch sts (Model SeqModel{..}) =
  Model $ SeqModel {
            modelAnchorToTip     = NE.length sts - (maybe (NE.length modelStates) NE.length modelNextSync - modelAnchorToTip)
          , modelAnchorsDistance
          , modelNextSync        = case modelNextSync of
              Nothing -> Just sts
              Just sy ->
                let trunk@(anchor NE.:| rest) = fromJust $ NE.nonEmpty (NE.take (NE.length sy - modelAnchorToTip) sy)
                in Just $ anchor NE.:| rest <> tail (NE.dropWhile (/= NE.last trunk) sts)
          , modelNextTicket
          , modelStates
          , modelTip
          , modelTxs
          }

transitions :: (
  blk ~ TestBlock,
    Show (Response blk r)
  , Show (Action blk r)
  , LedgerSupportsMempool blk
  )
  => LedgerConfig blk
  -> SeqModel blk r
  -> Action blk r
  -> Response blk r
  -> SeqModel blk r
transitions cfg model cmd resp = case model of
  NeedsInit -> case (cmd, resp) of
    (Init st, ResponseOk) ->
      Model $ SeqModel (getTickedTestLedger st NE.:| []) Nothing st 0 0 TxSeq.Empty (succ TxSeq.zeroTicketNo)

    _-> error "transitions: Model is not initialized"

  Model SeqModel{..} -> case (cmd, resp) of
      (TryAddTx tx, RespTryAddTx{}) -> tryAddTx tx $ (if modelAnchorsDistance > 0 then syncLedger cfg else id) model
      (SyncLedger{}, ResponseOk)    -> syncLedger cfg model
      (Switch sts,   SwitchedTo{})  -> switch sts model
      (Flush,        _)             -> if modelAnchorToTip > 0 then flush model else model


      (Init{},       _)              ->
        error "transitions: Model is re-initialized"
      _                              ->
        error $ "transitions: unexpected response " <> show resp <> " for command " <> show cmd

{-------------------------------------------------------------------------------
  Mock
-------------------------------------------------------------------------------}

mock :: LedgerConfig TestBlock
     -> SeqModel TestBlock Symbolic
     -> Action TestBlock Symbolic
     -> GenSym (Response TestBlock Symbolic)
mock cfg model action = case model of
  NeedsInit -> case action of
    Init{} -> pure ResponseOk
    _ -> error "mock: model not initialized"
  Model SeqModel{..} -> case action of
    Init{}     -> error "mock: model re-initialized"
    Flush      ->
      if modelAnchorToTip > 0
      then case modelNextSync of
        -- flush one of my current states
        Nothing -> pure $ Flushed $ modelStates NE.!! (NE.length modelStates - modelAnchorToTip)
        -- flush one of the next sync states
        Just v  -> pure $ Flushed $ v           NE.!! (NE.length v           - modelAnchorToTip)
      else pure ResponseOk
    Switch sts ->
      -- crop to the "volatile" suffix
      pure $ SwitchedTo $ fromJust $ NE.nonEmpty $ NE.drop (maybe (NE.length modelStates) NE.length modelNextSync - modelAnchorToTip - 1) sts
    SyncLedger -> pure ResponseOk
    TryAddTx t ->
      let TestGenTx tx tid = t
          baseLs = case (modelAnchorsDistance, modelNextSync) of
                 (0, _) -> modelTip
                 (_, Just ns) -> snd $ foldApplyTxs cfg ns (TxSeq.toList modelTxs)
                 (_, _) -> error "mismatch"
      in pure
       $ flip RespTryAddTx (modelTip `withLedgerTablesTicked` polyEmptyLedgerTables)
       $ Just
       $ case validate t baseLs of
           Left e   -> MempoolTxRejected t e
           Right () -> MempoolTxAdded $ TxSeq.TxTicket (TestValidatedTx tx tid) modelNextTicket 1

{-------------------------------------------------------------------------------
  Helpers for txs
-------------------------------------------------------------------------------}

-- | Apply a tx blindly
apply :: GenTx TestBlock -> TickedLedgerState TestBlock ValuesMK -> TickedLedgerState TestBlock ValuesMK
apply t ls =
  either (const ls) (const $
             TickedTestLedger
             $ TestLedger {
                payloadDependentState = UTxTok {
                    utxtoktables = TokenToTValue
                                   $ ApplyValuesMK $ DS.Values
                                   $ uncurry Map.insert (produced tx) $ Map.delete (consumed tx)
                                   $ values
                    , utxhist = Set.insert (fst (produced tx)) hist }
                , .. }
            ) (validate t ls)
 where
   TestGenTx tx _                  = t
   TickedTestLedger l              = ls
   TestLedger lastAppliedPoint pds = l
   UTxTok tbs hist                 = pds
   TokenToTValue (ApplyValuesMK (DS.Values values)) = tbs

-- | Validate a tx. Returns Right () on succesful validation
validate :: GenTx TestBlock -> TickedLedgerState TestBlock ValuesMK -> Either TxErr ()
validate t ls =
  if consumed tx `Map.member` values
  then if fst (produced tx) `Set.member` hist
       then Left $ TokenWasAlreadyCreated (fst (produced tx))
       else Right ()
  else Left $ TokenDoesNotExist (consumed tx)
  where
    TestGenTx tx _     = t
    TickedTestLedger l = ls
    TestLedger _ pds   = l
    UTxTok tbs hist    = pds
    TokenToTValue (ApplyValuesMK (DS.Values values)) = tbs

-- | validate and apply txs
foldApplyTxs :: LedgerConfig TestBlock
             -> NonEmpty (LedgerState TestBlock ValuesMK)
             -> [TxSeq.TxTicket (Validated (GenTx TestBlock))]
             -> (TxSeq (Validated (GenTx TestBlock)),
                  TickedLedgerState TestBlock ValuesMK)
foldApplyTxs cfg ns =
  foldl (\(sq, ls) tk@(TxSeq.TxTicket t _ _) ->
           case validate (txForgetValidated t) ls of
             Right () -> (sq TxSeq.:> tk, apply (txForgetValidated t) ls)
             _ -> (sq, ls)
        ) (TxSeq.Empty, tick cfg $ NE.last ns)

tick ::
  ( IsLedger (LedgerState blk)
  , TickedTableStuff (LedgerState blk)
  )
  => LedgerConfig blk
  -> LedgerState blk ValuesMK
  -> TickedLedgerState blk ValuesMK
tick cfg st = zipOverLedgerTablesTicked
                (flip rawApplyDiffs)
                (applyChainTick cfg (withOrigin 1 (+1) . pointSlot $ getTip st) (forgetLedgerTables st))
                (projectLedgerTables st)

{-# INLINE withOrigin'#-}
withOrigin' :: WithOrigin b -> b
withOrigin' = withOrigin (error "unexpected Origin!") id

{-------------------------------------------------------------------------------
  Generation
-------------------------------------------------------------------------------}

generator ::
     LedgerConfig TestBlock
  -> SeqModel TestBlock Symbolic
  -> Maybe (Gen (Action TestBlock Symbolic))
generator cfg = \case
  NeedsInit -> Just $ Init <$> (tick cfg <$> initialState)
  Model SeqModel{..}
      -- if the UTxO set is saturated
    | let pds = payloadDependentState $ getTickedTestLedger modelTip
          TokenToTValue (ApplyValuesMK (DS.Values vals)) = utxtoktables pds
      in Set.fromList (fmap Token [minBound..maxBound]) == Set.union (utxhist pds) (Map.keysSet vals)
    -> Just $ oneof [ genSwitch modelStates modelAnchorToTip modelNextSync
                    , pure Flush
                    , pure SyncLedger
                    ]
    | otherwise
    -> Just $ frequency $
         [ (3, do
               let ls = case (modelAnchorsDistance, modelNextSync) of
                     (0, _) -> getTickedTestLedger modelTip
                     (_, Just ns) -> NE.last ns
                     (_, _) -> error "mismatch"
               tid <- arbitrary
               TryAddTx . flip TestGenTx tid <$> frequency
                 [ (3, genSucceedingTransaction ls)
                 , (1, genNonExistingTransaction ls)
                 , (1, genDoubleCreatingTransaction ls)
                 ])
         , (1, genSwitch modelStates modelAnchorToTip modelNextSync)
         , (1, pure Flush)
         , (1, pure SyncLedger)
         ]

genSwitch :: NonEmpty (LedgerState TestBlock ValuesMK)
          -> Int
          -> Maybe (NonEmpty (LedgerState TestBlock ValuesMK))
          -> Gen (Action TestBlock r)
genSwitch modelStates modelAnchorToTip modelNextSync = Switch <$> do
  -- find the trunk from which we are forking
  let trunk = case modelNextSync of
                Nothing -> maybe (NE.head modelStates NE.:| []) id $ NE.nonEmpty $ NE.take (NE.length modelStates - modelAnchorToTip) modelStates
                Just sy -> maybe (NE.head sy NE.:| []) id $ NE.nonEmpty $ NE.take (NE.length sy - modelAnchorToTip) sy
  frequency
    [ (1, pure trunk)
    , (10, (trunk <>) <$> genListOfStates (NE.last trunk))
    ]

-- | Iteratively create a sequence of random states
genListOfStates :: LedgerState TestBlock ValuesMK
                  -> Gen (NonEmpty (LedgerState TestBlock ValuesMK))
genListOfStates firstState = do
    -- if generating many of these, there is a higher chance of saturating the utxo
    go (firstState, []) . getSmall . getPositive =<< (arbitrary :: Gen (Positive (Small Int)))
  where
    go (_, acc) 0 = pure $ fromJust $ NE.nonEmpty $ reverse acc
    go (prev, acc) n = Debug.trace ("next" <> show n) $ do

      nextValues <- nextRandomState prev
      go (nextValues, nextValues:acc) (n - 1)

{-------------------------------------------------------------------------------
  Preconditions
-------------------------------------------------------------------------------}

preconditions :: SeqModel blk Symbolic -> Action blk Symbolic -> Logic
-- When need init, only init
preconditions NeedsInit Init{} = Top
preconditions NeedsInit _      = Bot
-- Do not re-init
preconditions Model{}   Init{} = Bot -- Everything else is allowed
preconditions _ _ = Top

{-------------------------------------------------------------------------------
  Postconditions
-------------------------------------------------------------------------------}

postconditions :: Eq (Response TestBlock Concrete)
               => LedgerConfig TestBlock
               -> SeqModel TestBlock Concrete
               -> Action TestBlock Concrete
               -> Response TestBlock Concrete
               -> Logic
postconditions cfg model cmd resp =
   case cmd of
     Switch sts -> Annotate "Ledger tables at tip match" $ projectLedgerTables (NE.last sts) .== zipLedgerTables f (projectLedgerTables $ NE.head sts) (changelogFromStates sts)
     _ -> Top
  .&&
   case resp of
     _ -> Annotate "Responses match" (resp .== coerce (fst $ runGenSym (coerce mock cfg model cmd) newCounter))

  where
    f :: (Ord k, Eq v) => ValuesMK k v -> SeqDiffMK k v -> ValuesMK k v
    f (ApplyValuesMK dsValues) (ApplySeqDiffMK dseq)= ApplyValuesMK $ applyDiff dsValues (cumulativeDiff dseq)

parallelPostconditions :: Eq (Response TestBlock Concrete)
               => LedgerConfig TestBlock
               -> SeqModel TestBlock Concrete
               -> Action TestBlock Concrete
               -> Response TestBlock Concrete
               -> Logic
parallelPostconditions cfg model cmd resp =
   case (model, cmd, resp) of
     (Model SeqModel{}, Switch sts, SwitchedTo sts') -> projectLedgerTables (NE.last sts) .== zipLedgerTables f (projectLedgerTables $ NE.head sts') (changelogFromStates sts')
     _ -> Top
  .&&
  case resp of
    SwitchedTo{} -> Top -- I can't check equality due to concurrency (can I? in some interleaving?)
    RespTryAddTx res _ -> case coerce (fst $ runGenSym (coerce mock cfg model cmd) newCounter) of
      RespTryAddTx res' _ -> res .== res' -- I can't check equality on the ledger state used due to concurrency
      _ -> error "unmatched tryAddTxs"
    _ -> Annotate "Responses match" (resp .== coerce (fst $ runGenSym (coerce mock cfg model cmd) newCounter))

  where
    f :: (Ord k, Eq v) => ValuesMK k v -> SeqDiffMK k v -> ValuesMK k v
    f (ApplyValuesMK dsValues) (ApplySeqDiffMK dseq)= ApplyValuesMK $ applyDiff dsValues (cumulativeDiff dseq)

{-------------------------------------------------------------------------------
  Property
-------------------------------------------------------------------------------}

prop_mempoolSequential :: Property
prop_mempoolSequential = forAllCommands sm Nothing (theProperty sm)
  where
    cfg = defaultEraParams (SecurityParam 2) (slotLengthFromSec 2)

    sm = StateMachine
          initModel
          (transitions cfg)
          preconditions
          (postconditions cfg)
          Nothing
          (generator cfg)
          (const shrinkNothing)
          (semantics cfg)
          (mock cfg)
          noCleanup

theProperty ::
    StateMachine
      (SeqModel TestBlock)
      (Action TestBlock)
      (ReaderT (IORef a) IO)
      (Response TestBlock)
  -> Commands (Action TestBlock) (Response TestBlock)
  -> Property
theProperty = \sm cmds ->
    monadic (\p   -> ioProperty $ do
                ref <- newIORef undefined
                flip runReaderT ref p
            )
    (do
        (hist, _model, res) <- runCommands sm cmds
        prettyCommands sm hist (checkCommandNames cmds (res === Ok))
        )

prop_mempoolParallel :: Property
prop_mempoolParallel = forAllParallelCommands sm Nothing $ \cmds ->
    monadic (\p   -> counterexample (treeDraw cmds) $ ioProperty $ do
                putStrLn $ treeDraw cmds
                ref <- newIORef undefined
                flip runReaderT ref p
            )
            (runParallelCommandsNTimes 100 sm cmds
             >>= prettyParallelCommandsWithOpts cmds (Just (GraphOptions "./out.png" Png))) -- outputs png file
  where
    cfg = defaultEraParams (SecurityParam 2) (slotLengthFromSec 2)

    sm = StateMachine
      initModel
      (transitions cfg)
      preconditions
      (parallelPostconditions cfg)
      Nothing
      (generator cfg)
      (const shrinkNothing)
      (semantics cfg)
      (mock cfg)
      noCleanup

{-------------------------------------------------------------------------------
  Helpers for drawing and some specific test cases
-------------------------------------------------------------------------------}
treeDraw :: ParallelCommandsF Pair (Action TestBlock) (Response TestBlock) -> String
treeDraw (ParallelCommands prefix suffixes) =
  "\nTEST CASE\nPrefix\n" ++ (unlines $ map ('\t':) $ lines (tableString [def]
    unicodeRoundS
    def
    (map (\(Command c _ _) -> rowG [g c]) (unCommands prefix))
  )) ++ "\nParallel suffix\n" ++ (unlines $ map ('\t':) $ lines (tableString [def, def]
    unicodeRoundS
    def
    (map (\(Pair p1 p2) -> rowG [ f p1
                                , f p2]) suffixes)))

  where
    f (Commands cs) = intercalate "," $ map (\(Command c _ _) -> g c) cs
    g c = head $ words $ show c


myCase :: (QCGen, Int) -> IO ()
myCase seed = quickCheckWith (stdArgs {replay = Just seed}) $ prop_mempoolSequential

case1, case2 :: (QCGen, Int)
case2 = (read "SMGen 5390402246172236101 13325187111795903815", 54)
case1 = (read "SMGen 4081836451406931847 13827270112994510959", 25)

tests :: IO ()
tests = do
  res <- quickCheckResult $ withMaxSuccess 1_000_000 prop_mempoolSequential
  print (usedSeed res, usedSize res)
