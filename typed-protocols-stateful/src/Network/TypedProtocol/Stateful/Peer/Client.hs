{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators            #-}

-- | Bidirectional patterns for @'Peer' ps 'AsClient'@.   The advantage of
-- these patterns is that they automatically provide the 'RelativeAgencyEq'
-- singleton.
--
module Network.TypedProtocol.Stateful.Peer.Client
  ( Client
  , pattern Effect
  , pattern Yield
  , pattern Await
  , pattern Done
  , pattern YieldPipelined
  , pattern Collect
  , pattern CollectSTM
  , pattern CollectDone
    -- * re-exports
  , Pipelined (..)
  , Queue (..)
  ) where

import           Data.Kind (Type)
import           Data.Singletons

import           Network.TypedProtocol.Core
import           Network.TypedProtocol.Stateful.Peer (Peer)
import qualified Network.TypedProtocol.Stateful.Peer as TP


type Client :: forall ps
            -> Pipelined
            -> Queue ps
            -> ps
            -> (ps -> Type)
            -> (Type -> Type)
            -> (Type -> Type)
            -> Type
            -> Type
type Client ps pl q st f m stm a = Peer ps AsClient pl q st f m stm a


-- | Client role pattern for 'TP.Effect'.
--
pattern Effect :: forall ps pl q st f m stm a.
                  m (Client ps pl q st f m stm a)
               -- ^ monadic continuation
               -> Client ps pl q st f m stm a
pattern Effect mclient = TP.Effect mclient


-- | Client role pattern for 'TP.Yield'
--
pattern Yield :: forall ps pl st f m stm a.
                 ()
              => forall st'.
                 ( SingI (PeerHasAgency st)
                 , SingI (ProtocolState st')
                 , StateAgency st ~ ClientAgency
                 )
              => f st'
              -> Message ps st st'
              -- ^ protocol message
              -> Client ps pl Empty st' f m stm a
              -- ^ continuation
              -> Client ps pl Empty st  f m stm a
pattern Yield f msg k = TP.Yield ReflClientAgency f msg k


-- | Client role pattern for 'TP.Await'
--
pattern Await :: forall ps pl st f m stm a.
                 ()
              => ( SingI (PeerHasAgency st)
                 , StateAgency st ~ ServerAgency
                 )
              => (forall st'.
                     f st
                  -> Message ps st st'
                  -> ( Client ps pl Empty st' f m stm a
                     , f st'
                     )
                 )
              -- ^ continuation
              -> Client ps pl Empty st f m stm a
pattern Await k = TP.Await ReflServerAgency k


-- | Client role pattern for 'TP.Done'
--
pattern Done :: forall ps pl st f m stm a.
                ()
             => ( SingI (ProtocolState st)
                , StateAgency st ~ NobodyAgency
                )
             => a
             -- ^ protocol return value
             -> Client ps pl Empty st f m stm a
pattern Done a = TP.Done ReflNobodyAgency a


-- | Client role pattern for 'TP.YieldPipelined'
--
pattern YieldPipelined :: forall ps st q f m stm a.
                          ()
                       => forall st' st''.
                          ( SingI (PeerHasAgency st)
                          , SingI (ProtocolState st')
                          , StateAgency st ~ ClientAgency
                          )
                       => f st'
                       -> Message ps st st'
                       -- ^ pipelined message
                       -> Client ps 'Pipelined (q |> Tr st' st'') st'' f m stm a
                       -- ^ continuation
                       -> Client ps 'Pipelined  q                 st   f m stm a
pattern YieldPipelined f msg k = TP.YieldPipelined ReflClientAgency f msg k


-- | Client role pattern for 'TP.Collect'
--
pattern Collect :: forall ps st' st'' q st f m stm a.
                   ()
                => ( SingI (PeerHasAgency st')
                   , StateAgency st' ~ ServerAgency
                   )
                => Maybe (Client ps 'Pipelined (Tr st' st'' <| q) st f m stm a)
                -- ^ continuation, executed if no message has arrived so far
                -> (forall stNext.
                        f st'
                    -> Message ps st' stNext
                    -> ( Client ps 'Pipelined (Tr stNext st'' <| q) st f m stm a
                       , f stNext
                       )
                   )
                -- ^ continuation
                -> Client     ps 'Pipelined (Tr st'    st'' <| q) st f m stm a
pattern Collect k' k = TP.Collect ReflServerAgency k' k


-- | Client role pattern for 'TP.Collect'
--
pattern CollectSTM :: forall ps st' st'' q st f m stm a.
                      ()
                   => ( SingI (PeerHasAgency st')
                      , StateAgency st' ~ ServerAgency
                      )
                   => stm (Client ps 'Pipelined (Tr st' st'' <| q) st f m stm a)
                   -- ^ continuation, executed if no message has arrived so far
                   -> (forall stNext.
                         f st'
                      -> Message ps st' stNext
                      -> ( Client ps 'Pipelined (Tr stNext st'' <| q) st f m stm a
                         , f stNext
                         )
                      )
                   -- ^ continuation
                   -> Client     ps 'Pipelined (Tr st'    st'' <| q) st f m stm a
pattern CollectSTM k' k = TP.CollectSTM ReflServerAgency k' k


-- | Client role pattern for 'TP.CollectDone'
--
pattern CollectDone :: forall ps st q st' f m stm a.
                       ()
                    => ()
                    => Client ps 'Pipelined              q  st' f m stm a
                    -- ^ continuation
                    -> Client ps 'Pipelined (Tr st st <| q) st' f m stm a
pattern CollectDone k = TP.CollectDone k


{-# COMPLETE Effect, Yield, Await, Done, YieldPipelined, Collect, CollectDone #-}