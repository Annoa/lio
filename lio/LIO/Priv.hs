{-# LANGUAGE Unsafe #-}
{-# LANGUAGE DeriveDataTypeable #-}

module LIO.Priv (
  Priv(..)
  ) where

import safe Data.Typeable

-- Privileges
--

-- | A newtype wrapper that can be used by trusted code to transform a
-- powerless description of privileges into actual privileges.  The
-- constructor, 'PrivTCB', is dangerous as it allows creation of
-- arbitrary privileges.  Hence it is only exported by the unsafe
-- module "LIO.TCB".  A safe way to create arbitrary privileges is to
-- call 'privInit' (see "LIO.Run#v:privInit") from the 'IO' monad
-- before running your 'LIO' computation.
newtype Priv a = PrivTCB a deriving (Show, Eq, Typeable)

instance Monoid p => Monoid (Priv p) where
  mempty = PrivTCB mempty
  {-# INLINE mappend #-}
  mappend (PrivTCB m1) (PrivTCB m2) = PrivTCB $ m1 `mappend` m2
  {-# INLINE mconcat #-}
  mconcat ps = PrivTCB $ mconcat $ map (\(PrivTCB p) -> p) ps

