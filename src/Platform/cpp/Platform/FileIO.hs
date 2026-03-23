-----------------------------------------------------------------------------
-- Copyright 2024, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Platform-specific file I/O primitives.
    The cpp variant delegates to System.Directory, System.Process, etc.

    This module provides LOW-LEVEL primitives only. Higher-level functions
    (copyTextFile, searchPaths, etc.) live in Common.File and call these.
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
    -- * Home/temp directories
  , getHomeDirectory
  , getTemporaryDirectory
    -- * Process execution
  , runSystem, runSystemRaw, runCmd, runCmdRead, runCmdEnv
  ) where

import System.IO
import System.Directory( doesFileExist, doesDirectoryExist, createDirectoryIfMissing
                       , getCurrentDirectory, canonicalizePath, removeFile
                       , getFileSize
                       , getHomeDirectory, getTemporaryDirectory )
import System.Process   ( system, rawSystem, createProcess, CreateProcess(..)
                        , proc, StdStream(..), waitForProcess )
import System.Exit      ( ExitCode(..) )
import System.Environment ( getEnvironment, getExecutablePath )
import Data.Char( toLower )

import Common.Failure( raiseIO, catchIO )
import Platform.Config( pathSep, pathDelimiter )
import qualified Platform.Runtime as B ( exCatch )

-- ── File reading/writing ─────────────────────────────────────────────────────

readTextFile :: FilePath -> IO (Maybe String)
readTextFile fpath
  = B.exCatch (do content <- Prelude.readFile fpath
                  return (if null content then Just content else (seq (last content) $ Just content)))
              (\_ -> return Nothing)

writeTextFile :: FilePath -> String -> IO ()
writeTextFile = Prelude.writeFile

writeStringToFile :: FilePath -> String -> IO ()
writeStringToFile fpath content
  = do h <- openFile fpath WriteMode
       hPutStr h content `B.exCatch` (\_ -> return ())
       hClose h

readBinaryContents :: FilePath -> IO String
readBinaryContents fpath
  = withBinaryFile fpath ReadMode hGetContents

writeBinaryContents :: FilePath -> String -> IO ()
writeBinaryContents fpath content
  = withBinaryFile fpath WriteMode (\h -> hPutStr h content)

removeFileIfExists :: FilePath -> IO ()
removeFileIfExists fname
  = B.exCatch (removeFile fname) (\_ -> return ())

-- ── Paths and environment ────────────────────────────────────────────────────

getCwd :: IO FilePath
getCwd = canonicalizePath "."

realPath :: FilePath -> IO FilePath
realPath = canonicalizePath

getEnvVar :: String -> IO String
getEnvVar name
  = do env <- getEnvironment
       case lookup (map toLower name) (map (\(k,v) -> (map toLower k, v)) env) of
         Just val -> return val
         Nothing  -> return ""

getEnvPaths :: String -> IO [FilePath]
getEnvPaths name
  = do xs <- getEnvVar name
       return (splitDelim xs)
    `catchIO` \_ -> return []
  where
    splitDelim xs = filter (not . null) (split xs)
    split [] = [[]]
    split (c:cs)
      | c == ';' || c == pathDelimiter = [] : split cs
      | otherwise = case split cs of
                      (w:ws) -> (c:w) : ws
                      []     -> [[c]]

getProgramPath :: IO FilePath
getProgramPath = getExecutablePath

-- ── Process execution ────────────────────────────────────────────────────────

runSystemRaw :: String -> IO ()
runSystemRaw command
  = do exitCode <- system command
       case exitCode of
         ExitFailure _ -> raiseIO ("raw command failed:\n " ++ command)
         ExitSuccess   -> return ()

runSystem :: String -> IO ()
runSystem command
  = do exitCode <- system command
       case exitCode of
         ExitFailure _ -> raiseIO ("command failed:\n " ++ command)
         ExitSuccess   -> return ()

runCmd :: String -> [String] -> IO ()
runCmd cmd args
  = do exitCode <- rawSystem cmd args
       case exitCode of
          ExitFailure i -> raiseIO ("command failed (exit code " ++ show i ++ ")")
          ExitSuccess   -> return ()

runCmdRead :: [(String,String)] -> String -> [String] -> IO (String,String)
runCmdRead extraEnv cmd args
  = do mbEnv <- buildEnv extraEnv
       (_, Just hout, Just herr, process) <- createProcess (proc cmd args){ env = mbEnv, std_out = CreatePipe, std_err = CreatePipe }
       exitCode <- waitForProcess process
       case exitCode of
          ExitFailure i -> raiseIO ("command failed (exit code " ++ show i ++ ")")
          ExitSuccess   -> do out <- hGetContents hout
                              err <- hGetContents herr
                              return (out, err)

runCmdEnv :: [(String,String)] -> String -> [String] -> IO ()
runCmdEnv extraEnv cmd args
  = do mbEnv <- buildEnv extraEnv
       (_, _, _, process) <- createProcess (proc cmd args){ env = mbEnv }
       exitCode <- waitForProcess process
       case exitCode of
          ExitFailure i -> raiseIO ("command failed (exit code " ++ show i ++ ")")
          ExitSuccess   -> return ()

buildEnv :: [(String,String)] -> IO (Maybe [(String,String)])
buildEnv extraEnv
  = if null extraEnv then return Nothing
      else do oldEnv <- getEnvironment
              let newKeys = map fst extraEnv
              return (Just (extraEnv ++ filter (\(k,_) -> not (k `elem` newKeys)) oldEnv))
