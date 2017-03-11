{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE GADTs #-}

-- | This module implements and exports the functions exported by 'Run' in a
-- Continuation-Passing Style. For more information on its use see 'Run'.
--
-- This module is intended to be imported into your Main module, for
-- use in invoking 'LIO' code.  The functions are also available via
-- "LIO" and "LIO.Core", but those modules will clutter your namespace
-- with symbols you don't need in the 'IO' monad.
module LIO.CPS ( LIOState(..)
               , runLIO
               , tryLIO -- from LIO.Run
               , evalLIO -- from LIO.Run
               , privInit -- from LIO.Run
               ) where

import safe Control.Exception
import safe qualified Control.Exception as IO
import safe qualified Control.Concurrent as IO
import safe Data.IORef
import safe Data.Typeable
import safe Control.Monad
import safe qualified Data.Map as Map
import safe Data.Unique
import safe Control.Monad.Cont

import safe LIO.Exception (throwLIO)
import safe LIO.Error
import safe LIO.Label

import LIO.TCB.MLabel
import LIO.TCB

import LIO.Run (tryLIO, evalLIO, privInit)

-- | Execute an 'LIO' action, returning its result and the final label
-- state as a pair.  Note that it returns a pair whether or not the
-- 'LIO' action throws an exception.  Forcing the result value will
-- re-throw the exception, but the label state will always be valid.
--
-- See also 'evalLIO'.
runLIO :: Label l => LIO l a -> LIOState l -> IO (a, LIOState l)
runLIO lio_ s0 = do
  sp <- newIORef s0
  a <- runContT (runLIO' sp lio_) return
         `IO.catch` \e -> return $ throw $ makeCatchable e
  s1 <- readIORef sp
  return (a, s1)
  where
    runLIO' :: Label l => IORef (LIOState l) -> LIO l a -> ContT r IO a
    runLIO' ioRef lio =  case lio of
      -- * Internal State
      -- ** Labels
      GetLabel      -> runLIO' ioRef $ lioLabel `liftM` GetLIOStateTCB

      SetLabel l    -> runLIO' ioRef $
        WithContext "setLabel" $ do
          GuardAlloc l
          ModifyLIOStateTCB $ \s -> s { lioLabel = l }

      SetLabelP p l -> runLIO' ioRef $
         WithContext "setLabelP" $ do
           GuardAllocP p l
           ModifyLIOStateTCB $ \s -> s { lioLabel = l }

      -- ** Clearances
      GetClearance -> runLIO' ioRef $ lioClearance `liftM` GetLIOStateTCB

      SetClearance cnew -> runLIO' ioRef $ do
        LIOState { lioLabel = l, lioClearance = c } <- GetLIOStateTCB
        unless (canFlowTo l cnew && canFlowTo cnew c) $
          labelError "setClearance" [cnew]
        PutLIOStateTCB $ LIOState l cnew

      SetClearanceP p cnew -> runLIO' ioRef $ do
        LIOState l c <- GetLIOStateTCB
        unless (canFlowTo l cnew && canFlowToP p cnew c) $
          labelErrorP "setClearanceP" p [cnew]
        PutLIOStateTCB $ LIOState l cnew

      ScopeClearance action -> do
        LIOState _ c <- liftIO $ readIORef ioRef
        ea <- liftIO $ IO.try $ runContT (runLIO' ioRef action) return
        LIOState l _ <- liftIO $ readIORef ioRef
        liftIO $ writeIORef ioRef (LIOState l c)
        if l `canFlowTo` c
          then either (liftIO . IO.throwIO :: SomeException -> ContT r IO a)
                      return ea
          else liftIO $ IO.throwIO LabelError
                      { lerrContext = []
                      , lerrFailure = "scopeClearance"
                      , lerrCurLabel = l
                      , lerrCurClearance = c
                      , lerrPrivs = []
                      , lerrLabels = [] }

      WithClearance c lio' -> runLIO' ioRef $
        ScopeClearance $ SetClearance c >> lio'

      WithClearanceP p c lio' -> runLIO' ioRef $
        ScopeClearance $ SetClearanceP p c >> lio'

      -- * Guards
      -- ** Allocation
      GuardAlloc newl -> runLIO' ioRef $ do
        LIOState { lioLabel = l, lioClearance = c } <- GetLIOStateTCB
        unless (canFlowTo l newl && canFlowTo newl c) $
          labelError "guardAllocP" [newl]

      GuardAllocP p newl -> runLIO' ioRef $ do
        LIOState { lioLabel = l, lioClearance = c } <- GetLIOStateTCB
        unless (canFlowToP p l newl && canFlowTo newl c) $
          labelErrorP "guardAllocP" p [newl]

      -- ** Read
      Taint newl -> runLIO' ioRef $ do
        LIOState { lioLabel = l, lioClearance = c } <- GetLIOStateTCB
        let l' = l `lub` newl
        unless (l' `canFlowTo` c) $ labelError "taint" [newl]
        ModifyLIOStateTCB $ \s -> s { lioLabel = l' }

      TaintP p newl -> runLIO' ioRef $ do
        LIOState { lioLabel = l, lioClearance = c } <- GetLIOStateTCB
        let l' = l `lub` downgradeP p newl
        unless (l' `canFlowTo` c) $ labelErrorP "taintP" p [newl]
        ModifyLIOStateTCB $ \s -> s { lioLabel = l' }

      GuardWrite newl -> runLIO' ioRef $
        WithContext "guardWrite" $ do
        GuardAlloc newl
        Taint newl

      GuardWriteP p newl -> runLIO' ioRef $
        WithContext "guardWriteP" $ do
        GuardAllocP p newl
        TaintP p newl

      -- * Monadic actions
      Return a -> return a
      Bind ma k -> runLIO' ioRef ma >>= runLIO' ioRef . k
      Fail s -> fail s

      -- * Internal state
      GetLIOStateTCB -> liftIO $ readIORef ioRef
      PutLIOStateTCB s -> liftIO $ writeIORef ioRef s
      ModifyLIOStateTCB f -> do
        s <- liftIO $ readIORef ioRef
        liftIO $ writeIORef ioRef (f s)

      -- * IO lift
      IoTCB a -> liftIO a

      -- * Exception handling
      Catch lio' h ->
        liftIO $ IO.catch (runContT (runLIO' ioRef lio') return)
               $ \e -> runContT (runLIO' ioRef (safe e)) return
        where
          uncatchableType = typeOf (undefined :: UncatchableTCB)
          safe e@(SomeException einner) = do
            when (typeOf einner == uncatchableType) $ throwLIO e
            LIOState l c <- getLIOStateTCB
            unless (l `canFlowTo` c) $ throwLIO e
            maybe (throwLIO e) h $ fromException e

      -- * Error handling
      WithContext ctx lio' ->
        liftIO . IO.catch (runContT (runLIO' ioRef lio') return) $ \e ->
          liftIO . IO.throwIO . annotate ctx $ (e :: AnyLabelError)

      -- * Concurrent handling
      ForkLIO lio' -> runLIO' ioRef $ do
        s <- GetLIOStateTCB
        IoTCB $ void $ IO.forkIO $ do
          ((), _) <- runLIO lio' s
          return ()

      LForkP p l action -> runLIO' ioRef $ do
        withContext "lForkP" $ GuardAllocP p l
        mv <- IoTCB IO.newEmptyMVar
        st <- IoTCB $ newIORef LResEmpty
        s' <- GetLIOStateTCB
        tid <- IoTCB $ IO.mask $ \unmask -> IO.forkIO $ do
          sp <- newIORef s'
          ea <- IO.try $ unmask $ runContT (runLIO' sp action) return
          LIOState lEnd _ <- liftIO $ readIORef sp
          writeIORef st $ case ea of
            _ | not (lEnd `canFlowTo` l) -> LResLabelTooHigh lEnd
            Left e                       -> LResResult $ IO.throw $
                                               makeCatchable e
            Right a                      -> LResResult a
          IO.putMVar mv ()
        return $ LabeledResultTCB tid l mv st

      LWaitP p (LabeledResultTCB _ l mv st) -> runLIO' ioRef $
        withContext "lWaitP" (TaintP p l) >> go
        where go = IoTCB (readIORef st) >>= check
              check LResEmpty = ioTCB (IO.readMVar mv) >> go
              check (LResResult a) = return $! a
              check (LResLabelTooHigh lnew) = do
                modifyLIOStateTCB $ \s -> s {
                    lioLabel = downgradeP p lnew `lub` lioLabel s }
                throwLIO ResultExceedsLabel {
                    relContext = []
                  , relLocation = "lWaitP"
                  , relDeclaredLabel = l
                  , relActualLabel = Just lnew }

      TrylWaitP p (LabeledResultTCB _ rl _ st) -> runLIO' ioRef $
        withContext "trylWaitP" (TaintP p rl) >> ioTCB (readIORef st) >>= check
        where check LResEmpty = return Nothing
              check (LResResult a) = return . Just $! a
              check (LResLabelTooHigh lnew) = do
                curl <- GetLabel
                if canFlowToP p lnew curl
                  then throwLIO ResultExceedsLabel {
                          relContext = []
                        , relLocation = "trylWaitP"
                        , relDeclaredLabel = rl
                        , relActualLabel = Just lnew }
                  else return Nothing

      TimedlWaitP p lr@(LabeledResultTCB t rl mvb _) to -> runLIO' ioRef $
        withContext "timedlWaitP" $ do GuardWriteP p rl
                                       TrylWaitP p lr >>= go
        where go (Just a) = return a
              go Nothing = do
                mvk <- IoTCB IO.newEmptyMVar
                tk <- IoTCB $ IO.forkIO $ IO.finally (IO.threadDelay to) $ do
                  IO.putMVar mvk ()
                  IO.throwTo t (UncatchableTCB IO.ThreadKilled)
                IoTCB $ IO.readMVar mvb
                TrylWaitP p lr >>= maybe
                  (IoTCB (IO.takeMVar mvk) >> throwLIO failure)
                  (\a -> IoTCB (IO.killThread tk) >> return a)
              failure = ResultExceedsLabel { relContext = []
                                           , relLocation = "timedWaitP"
                                           , relDeclaredLabel = rl
                                           , relActualLabel = Nothing }

      WithMLabelP  p (MLabelTCB ll r mv _) action -> do
        runLIO' ioRef (TaintP p ll)
        tid <- liftIO IO.myThreadId
        u <- liftIO newUnique
        let check lnew = do
              LIOState { lioLabel = lcur, lioClearance = ccur } <-
                liftIO $ readIORef ioRef
              if canFlowToP p lcur lnew && canFlowToP p lnew lcur
                then return True
                else do IO.throwTo tid LabelError {
                            lerrContext = []
                          , lerrFailure = "withMLabelP label changed"
                          , lerrCurLabel = lcur
                          , lerrCurClearance = ccur
                          , lerrPrivs = [GenericPrivDesc $ privDesc p]
                          , lerrLabels = [lnew]   }
                        return False
            enter = IO.modifyMVar_ mv $ \m -> do
              void $ readIORef r >>= check
              return $ Map.insert u check m
            exit = IO.modifyMVar_ mv $ return . Map.delete u
        liftIO $ IO.bracket_ enter exit
               $ runContT (runLIO' ioRef action) return

      ModifyMLabelP p (MLabelTCB ll r mv pl) fn -> runLIO' ioRef $
        withContext "modifyMLabelP" $ do
          GuardWriteP p ll
          IoTCB $ IO.modifyMVar_ mv $ \m -> do
            lold <- liftIO $ readIORef r
            lnew <- runContT (runLIO' ioRef $ fn lold) return
            () <- runContT (runLIO' ioRef $ mlabelPolicy pl p lold lnew) return
            writeIORef r lnew
            Map.fromList `fmap` filterM (($ lnew) . snd) (Map.assocs m)
