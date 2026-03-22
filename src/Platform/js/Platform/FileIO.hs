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
    -- * File existence and metadata
    doesFileExist
  , doesDirectoryExist
  , createDirectoryIfMissing
  , getFileSize
    -- * File reading and writing
  , readTextFile
  , writeTextFile
  , writeStringToFile
  , readBinaryContents
  , writeBinaryContents
  , removeFileIfExists
    -- * Paths and environment
  , getCwd
  , realPath
  , getEnvVar
  , getEnvPaths
  , getProgramPath
    -- * Process execution
  , runSystem, runSystemRaw, runCmd, runCmdRead, runCmdEnv
  ) where

import GHC.JS.Prim (JSVal, toJSString, fromJSString, isNull, isUndefined)
import Common.Failure( raiseIO )

-- ── File existence and metadata ──────────────────────────────────────────────

doesFileExist :: FilePath -> IO Bool
doesFileExist fpath = js_vfsFileExists (toJSString fpath)

doesDirectoryExist :: FilePath -> IO Bool
doesDirectoryExist _ = return True

createDirectoryIfMissing :: Bool -> FilePath -> IO ()
createDirectoryIfMissing _ _ = return ()

getFileSize :: FilePath -> IO Integer
getFileSize fpath = do
  n <- js_vfsFileSize (toJSString fpath)
  return (fromIntegral n)

-- ── File reading and writing ─────────────────────────────────────────────────

readTextFile :: FilePath -> IO (Maybe String)
readTextFile fpath = do
  result <- js_vfsReadFile (toJSString fpath)
  if isNull result || isUndefined result
    then return Nothing
    else return (Just (fromJSString result))

writeTextFile :: FilePath -> String -> IO ()
writeTextFile fpath content = js_vfsWriteFile (toJSString fpath) (toJSString content)

writeStringToFile :: FilePath -> String -> IO ()
writeStringToFile = writeTextFile

readBinaryContents :: FilePath -> IO String
readBinaryContents fpath = do
  mb <- readTextFile fpath
  case mb of
    Just s  -> return s
    Nothing -> error ("unable to read " ++ fpath)

writeBinaryContents :: FilePath -> String -> IO ()
writeBinaryContents = writeTextFile

removeFileIfExists :: FilePath -> IO ()
removeFileIfExists fpath = js_vfsRemoveFile (toJSString fpath)

-- ── Paths and environment ────────────────────────────────────────────────────

getCwd :: IO FilePath
getCwd = return "/"

realPath :: FilePath -> IO FilePath
realPath fpath = return fpath  -- no canonicalization on JS

getEnvVar :: String -> IO String
getEnvVar _ = return ""

getEnvPaths :: String -> IO [FilePath]
getEnvPaths _ = return []

getProgramPath :: IO FilePath
getProgramPath = return "/koka"

-- ── Process execution (all unsupported on JS) ────────────────────────────────

runSystemRaw :: String -> IO ()
runSystemRaw _ = raiseIO "command execution not available in browser"

runSystem :: String -> IO ()
runSystem _ = raiseIO "command execution not available in browser"

runCmd :: String -> [String] -> IO ()
runCmd _ _ = raiseIO "command execution not available in browser"

runCmdRead :: [(String,String)] -> String -> [String] -> IO (String,String)
runCmdRead _ _ _ = raiseIO "command execution not available in browser"

runCmdEnv :: [(String,String)] -> String -> [String] -> IO ()
runCmdEnv _ _ _ = raiseIO "command execution not available in browser"

-- ── JS FFI ───────────────────────────────────────────────────────────────────

foreign import javascript unsafe "h$kokaVfsFileExists"
  js_vfsFileExists :: JSVal -> IO Bool

foreign import javascript unsafe "h$kokaVfsFileSize"
  js_vfsFileSize :: JSVal -> IO Int

foreign import javascript safe "h$kokaVfsReadFile"
  js_vfsReadFile :: JSVal -> IO JSVal

foreign import javascript unsafe "h$kokaVfsWriteFile"
  js_vfsWriteFile :: JSVal -> JSVal -> IO ()

foreign import javascript unsafe "h$kokaVfsRemoveFile"
  js_vfsRemoveFile :: JSVal -> IO ()
