-----------------------------------------------------------------------------
-- Copyright 2024, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Platform-specific file I/O primitives.
    The cpp variant delegates to System.Directory and System.IO.
-}
-----------------------------------------------------------------------------
module Platform.FileIO(
    doesFileExist
  , doesDirectoryExist
  , createDirectoryIfMissing
  , writeStringToFile
  ) where

import System.Directory( doesFileExist, doesDirectoryExist, createDirectoryIfMissing )
import System.IO( openFile, hPutStr, hClose, IOMode(..) )
import Platform.Runtime( finally )

-- | Write a string to a file (using file handles on native, VFS on JS)
writeStringToFile :: FilePath -> String -> IO ()
writeStringToFile fpath content
  = do h <- openFile fpath WriteMode
       hPutStr h content `finally` hClose h
