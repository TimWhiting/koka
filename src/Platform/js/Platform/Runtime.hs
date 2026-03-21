------------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Module that exports non-standardized functions.
    (GHC JavaScript backend variant: uses standard GHC implementations)
-}
-----------------------------------------------------------------------------
module Platform.Runtime( exCatch
                       , unsafePerformIO
                       , finally
                       -- , copyBinaryFile
                       , showHFloat
                       ) where

import System.IO.Unsafe( unsafePerformIO )
import System.IO.Error ( ioeGetErrorString )
import Control.Exception( finally )
import qualified Control.Exception as Ex
import Numeric( showHFloat )

exCatch :: IO a -> (String -> IO a) -> IO a
exCatch io handler
  = Ex.catches io [Ex.Handler (\(Ex.ErrorCall msg)  -> handler msg)
                  ,Ex.Handler (\(err) -> handler (ioeGetErrorString (err :: IOError)))
                  ,Ex.Handler (\(err) -> handler (show (err :: Ex.SomeException)))]
