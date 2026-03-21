------------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Reading file times.
    (GHC JavaScript backend variant: IO functions are stubbed)
-}
-----------------------------------------------------------------------------
module Platform.Filetime( FileTime
                       , getCurrentTime
                       , getFileTime
                       , getFileTimeOrCurrent
                       , setFileTime
                       , fileTime0
                       , fileTimeToPicoseconds
                       , showTimeDiff
                       ) where

import qualified Data.Time as T
import qualified Data.Ratio as R
import Platform.Runtime( exCatch )

type FileTime = T.UTCTime

getCurrentTime :: IO FileTime
getCurrentTime
  = T.getCurrentTime

fileTime0 :: FileTime
fileTime0
  = T.UTCTime (T.ModifiedJulianDay 0) (T.secondsToDiffTime 0)

showTimeDiff :: FileTime -> FileTime -> String
showTimeDiff t1 t0
  = show (T.diffUTCTime t1 t0)

fileTimeToPicoseconds :: FileTime -> Integer
fileTimeToPicoseconds t
  = diffTimeToPicoseconds (T.utctDayTime t)

diffTimeToPicoseconds :: T.DiffTime -> Integer
diffTimeToPicoseconds t
  = R.numerator (toRational t * 1000000000000)

-- | Returns the file modification time or 0 if it does not exist.
getFileTime :: FilePath -> IO FileTime
getFileTime _fname
  = return fileTime0

-- | Set the file modification time
setFileTime :: FilePath -> FileTime -> IO ()
setFileTime _fname _ftime
  = return ()

-- | returns the file modification time or the current time if it does not exist.
getFileTimeOrCurrent :: FilePath -> IO FileTime
getFileTimeOrCurrent _fname
  = getCurrentTime
