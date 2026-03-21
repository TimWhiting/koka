------------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Module that exports non-standardized 'MVar's.
    (GHC JavaScript backend variant: uses IORef implementation)
-}
-----------------------------------------------------------------------------
module Platform.Var( Var, newVar, takeVar, putVar
                   ) where

import Data.IORef

type Var a = IORef a

newVar :: a -> IO (Var a)
newVar   = newIORef

putVar :: Var a -> a -> IO ()
putVar   = writeIORef

takeVar :: Var a -> IO a
takeVar  = readIORef
