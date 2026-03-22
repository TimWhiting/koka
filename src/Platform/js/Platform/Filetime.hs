------------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Reading file times.
    (GHC JavaScript backend variant: delegates to kokaVFS.fileTime via FFI)
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
import GHC.JS.Prim (JSVal, toJSString)
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

-- | Returns the file modification time or fileTime0 if it does not exist.
-- Delegates to globalThis.kokaVFS.fileTime which returns milliseconds since epoch.
getFileTime :: FilePath -> IO FileTime
getFileTime fname
  = do ms <- js_vfsFileTime (toJSString fname)
       if ms <= 0
         then return fileTime0
         else return (msToUTCTime ms)

-- | Set the file modification time (no-op on JS, VFS is managed by frontend)
setFileTime :: FilePath -> FileTime -> IO ()
setFileTime _fname _ftime
  = return ()

-- | Returns the file modification time or the current time if it does not exist.
getFileTimeOrCurrent :: FilePath -> IO FileTime
getFileTimeOrCurrent fname
  = do t <- getFileTime fname
       if t == fileTime0 then getCurrentTime else return t

-- Convert milliseconds since epoch to UTCTime
msToUTCTime :: Double -> T.UTCTime
msToUTCTime ms =
  let secs = ms / 1000.0
      days = floor (secs / 86400.0) :: Integer
      dayFrac = secs - fromIntegral (days * 86400)
      -- POSIX epoch is Modified Julian Day 40587
      mjd = T.ModifiedJulianDay (days + 40587)
  in T.UTCTime mjd (T.picosecondsToDiffTime (round (dayFrac * 1e12)))

foreign import javascript unsafe "h$kokaVfsFileTime"
  js_vfsFileTime :: JSVal -> IO Double
