{-# LANGUAGE Unsafe #-}
module LIO.TCB.MLabel (
  MLabel(..)
  ) where

import safe Data.IORef
import safe Data.Map (Map)
import safe Data.Typeable
import safe Data.Unique
import safe Control.Concurrent.MVar

-- | A mutable label.  Consists of a static label on the label, a
-- mutable label, and a list of threads currently accessing the label.
-- This is intended to be used by privileged code implementing @IO@
-- abstractions with mutable labels.  Routines for accessing such an
-- @IO@ abstraction should perform tne @IO@ from within a call to
-- 'withMLabelP', to ensure an exception is raised if another thread
-- revokes access with 'modifyMLabelP'.
data MLabel policy l = MLabelTCB {
    mlLabelLabel :: !l
  , mlLabel :: !(IORef l)
  , mlUsers :: !(MVar (Map Unique (l -> IO Bool)))
  , mlPolicy :: policy
  } deriving (Typeable)
