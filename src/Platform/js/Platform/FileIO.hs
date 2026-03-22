-----------------------------------------------------------------------------
-- Copyright 2024, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Platform-specific file I/O primitives.
    The JS variant delegates to globalThis.kokaVFS via FFI.
-}
-----------------------------------------------------------------------------
module Platform.FileIO(
    doesFileExist
  , doesDirectoryExist
  , createDirectoryIfMissing
  , writeStringToFile
  ) where

import GHC.JS.Prim (JSVal, toJSString)

-- | Check if a file exists in the VFS
doesFileExist :: FilePath -> IO Bool
doesFileExist fpath = js_vfsFileExistsRaw (toJSString fpath)

-- | Directories always "exist" in the VFS
doesDirectoryExist :: FilePath -> IO Bool
doesDirectoryExist _ = return True

-- | No-op on JS
createDirectoryIfMissing :: Bool -> FilePath -> IO ()
createDirectoryIfMissing _ _ = return ()

-- | Write a string to the VFS
writeStringToFile :: FilePath -> String -> IO ()
writeStringToFile fpath content = js_vfsWriteFileRaw (toJSString fpath) (toJSString content)

foreign import javascript unsafe "h$kokaVfsFileExists"
  js_vfsFileExistsRaw :: JSVal -> IO Bool

foreign import javascript unsafe "h$kokaVfsWriteFile"
  js_vfsWriteFileRaw :: JSVal -> JSVal -> IO ()
