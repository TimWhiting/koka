-----------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Internal errors and assertions.
-}
{-# OPTIONS -cpp #-}
-----------------------------------------------------------------------------
module Common.File(
                  -- * System
                    getEnvPaths, getEnvVar
                  , searchPaths, searchPathsSuffixes, searchPathsEx, searchPathsCanonical
                  , getMaximalPrefixPath
                  , searchProgram
                  , runSystem, runSystemRaw, runCmd, runCmdRead, runCmdEnv
                  , getProgramPath

                  -- * Strings
                  , startsWith, endsWith, splitOn, trim

                  -- * File names
                  , FileName
                  , basename, notdir, notext, joinPath, joinPaths, extname, dirname, noexts
                  , splitPath, undelimPaths
                  , isPathSep, isPathDelimiter
                  , findMaximalPrefixPath
                  , isAbsolute
                  , commonPathPrefix
                  , normalizeWith, normalize
                  , isLiteralDoc
                  , ensureExt

                  -- * Files
                  , FileTime, fileTime0, maxFileTime, maxFileTimes, showTimeDiff
                  , fileTimeCompare, getFileTime
                  , getFileTimeOrCurrent, getCurrentTime
                  , readTextFile, writeTextFile
                  , copyTextFile, copyTextIfNewer, copyTextIfNewerWith, copyTextFileWith
                  , copyBinaryFile, copyBinaryIfNewer
                  , removeFileIfExists
                  , realPath
                  , doesFileExistAndNotEmpty
                  , makeRelativeToPaths
                  , getCwd
                  , relativeToPath
                  , seqList, seqMaybe, seqEither, seqTuple2, seqString
                  , seqqList, seqqMaybe, seqqEither, seqqTuple2, seqqString
                  ) where

import Data.List        ( intersperse, isPrefixOf, maximumBy )
import Data.Char        ( toLower, isSpace )
import Platform.Config  ( pathSep, pathDelimiter, sourceExtension, exeExtension )
import qualified Platform.Runtime as B ( {- copyBinaryFile, -} exCatch )
import Common.Failure   ( raiseIO, catchIO )

#ifndef KOKA_WEB
import System.IO
import System.Process   ( system, rawSystem, createProcess, CreateProcess(..), proc, StdStream(..), waitForProcess )
import System.Exit      ( ExitCode(..) )
import System.Environment ( getEnvironment, getExecutablePath )
import System.Directory ( doesFileExist, doesDirectoryExist
                        {- , copyFile, copyFileWithMetadata -}
                        , getCurrentDirectory, getDirectoryContents
                        , createDirectoryIfMissing, canonicalizePath, removeFile, getFileSize )
#endif

#ifdef KOKA_WEB
import GHC.JS.Prim (JSVal, toJSString, fromJSString, toJSArray, fromJSArray, isNull, isUndefined)
#endif

import Debug.Trace
import Platform.Filetime

seqList :: [a] -> b -> b
seqList [] b     = b
seqList (x:xs) b = seq x (seqList xs b)

seqMaybe :: Maybe a -> b -> b
seqMaybe Nothing  b = b
seqMaybe (Just x) b = seq x b

seqEither :: Either a b -> c -> c
seqEither (Left x) z  = seq x z
seqEither (Right y) z = seq y z

seqTuple2 :: (a,b) -> c -> c
seqTuple2 (x,y) z  = seq x (seq y z)

seqString :: String -> a -> a
seqString s z = if null s then z else seq (last s) z

-- use seqqXXX when assigning to a field that is already strict
seqqList :: [a] -> [a]
seqqList xs  = seqList xs xs

seqqMaybe :: Maybe a -> Maybe a
seqqMaybe x  = seqMaybe x x

seqqEither :: Either a b -> Either a b
seqqEither x  = seqEither x x

seqqTuple2 :: (a,b) -> (a,b)
seqqTuple2 x  = seqTuple2 x x

seqqString :: String -> String
seqqString s = seqString s s

startsWith, endsWith :: String -> String -> Bool
startsWith s  [] = True
startsWith [] _  = False
startsWith (c:cs) (p:ps) = if (p==c) then startsWith cs ps else False

endsWith s post
  = startsWith (reverse s) (reverse post)

splitOn pred xs
  = normalize [] xs
  where
    normalize acc [] = reverse acc
    normalize acc xs
      = case (span (not . pred) xs) of
          (pre,post) -> normalize (pre:acc) (dropWhile pred post)


trim s
  = reverse $ dropWhile isSpace $ reverse $ dropWhile isSpace $ s

isLiteralDoc :: FileName -> Bool
isLiteralDoc fname
  = endsWith fname (sourceExtension ++ ".md") ||
    endsWith fname (sourceExtension ++ ".mdk")

{--------------------------------------------------------------------------
  File names
--------------------------------------------------------------------------}
-- | File name
type FileName = FilePath

-- | Remove the extension and directory part
basename :: FileName -> FileName
basename fname
  = case dropWhile (/='.') (reverse (notdir fname)) of
      '.':rbase -> reverse rbase
      _         -> notdir fname


-- | Get the file extension
extname :: FileName -> FileName
extname fname
  = let (pre,post) = span (/='.') (reverse (notdir fname))
    in if null post
        then ""
        else ("." ++ reverse pre)

ensureExt :: FileName -> String -> FileName
ensureExt fname ext
  = if (extname fname == ext) then fname else fname ++ ext

-- | Return the directory prefix (including last separator if present)
dirname :: FileName -> FileName
dirname fname
  = joinPaths (init (splitPath fname))

-- | Remove the directory prefix
notdir :: FileName -> FileName
notdir fname
  = last (splitPath fname)


notext :: FileName -> FileName
notext fname
  = reverse (drop (length (extname fname)) (reverse fname))

noexts :: FileName -> FileName
noexts fname
  = joinPaths [dirname fname, takeWhile (/='.') (notdir fname)]

-- | Split a (semi-)colon separated list of directories into a directory list
undelimPaths :: String -> [FilePath]
undelimPaths xs
  = filter (not . null) (normalize [] "" xs)
  where
    -- initial spaces
    normalize ps "" (c:cs)  | isSpace c
      = normalize ps "" cs
    -- directory on windows
    normalize ps "" (c:':':cs)
      = normalize ps (':':c:[]) cs
    -- normal
    normalize ps p xs
      = case xs of
          []     -> if (null p)
                     then reverse ps
                     else reverse (reverse p:ps)
          (c:cs) | isPathDelimiter c -> normalize (reverse p:ps) "" cs
                 | otherwise         -> normalize ps (c:p) cs

-- | Split a path into its directory parts
splitPath :: FilePath -> [FilePath]
splitPath fdir
  = case normalize fdir of
      "" -> [""]
      '/':'/':fs -> "//":split fs
      '/':fs -> "/":split fs
      fs -> split fs
  where
    split f = splitOn isPathSep f

onWindows :: Bool
onWindows
  = (exeExtension == ".exe")


joinPath :: FilePath -> FilePath -> FilePath
joinPath p1 p2
  = joinPaths [p1,p2]

-- | Join a list of paths into one path
joinPaths :: [FilePath] -> FilePath
joinPaths dirs
  = concat
  $ filterPathSepDup
  $ intersperse ['/']
  $ resolveDot
  $ concatMap splitPath
  $ filter (not . null) dirs
  where
    resolveDot []            = []
    resolveDot (p:".":ps)    = resolveDot (p:ps)
    resolveDot (p:"..":ps)   | p == "."  = resolveDot ("..":ps)
                            | p == ".." = p : resolveDot ("..":ps)
                            | otherwise = resolveDot ps
    resolveDot (p:ps)        = p : resolveDot ps


    filterPathSepDup (p:q:rest)  | endsWith p "/" && q == "/"  = filterPathSepDup (p : rest)
    filterPathSepDup (p:ps)      = p : filterPathSepDup ps
    filterPathSepDup []          = []

-- | Normalize path separators
normalize :: FilePath -> FilePath
normalize path
  = case normalizeWith '/' path of
      (c:':':'/':rest) -> [toLower c] ++ ":/" ++ rest  -- use lower case drive letters on windows
      npath            -> npath

-- | Normalize path separators with a specified path separator
normalizeWith :: Char -> FilePath -> FilePath
normalizeWith newSep path
  = norm "" path
  where
    norm acc "" = reverse acc
    norm acc ('\\':c:cs) | isSpace c -- escaped space on unix/macos
      = norm (c:'\\':acc) cs
    norm acc (c:cs)
      = if (isPathSep c)
         then norm (newSep:acc) cs
         else norm (c:acc) cs


-- | Is this a file separator?
isPathSep :: Char -> Bool
isPathSep c
  = (c == '/' || c == '\\')

-- | Is this a path delimiter? (@;@ (and @:@ too on unix)
isPathDelimiter :: Char -> Bool
isPathDelimiter c
  = (c == ';' || c == pathDelimiter)

#ifdef KOKA_WEB
getCwd :: IO FilePath
getCwd = return "/"
#else
getCwd :: IO FilePath
getCwd
   = realPath "."
#endif

{--------------------------------------------------------------------------
  system
--------------------------------------------------------------------------}

#ifdef KOKA_WEB
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

buildEnv :: [(String,String)] -> IO (Maybe [(String,String)])
buildEnv _ = return Nothing
#else
runSystemRaw :: String -> IO ()
runSystemRaw command
  = do -- putStrLn ("system: " ++ command)
       exitCode <- system command
       case exitCode of
         ExitFailure i -> raiseIO ("raw command failed:\n " ++ command )
         ExitSuccess   -> return ()

runSystem :: String -> IO ()
runSystem command0
  = do -- putStrLn ("system: " ++ command)
       let command = normalizeWith pathSep command0
       exitCode <- system command
       case exitCode of
         ExitFailure i -> raiseIO ("command failed:\n " ++ command )
         ExitSuccess   -> return ()

runCmd :: String -> [String] -> IO ()
runCmd cmd args
  = do -- putStrLn ("run command: " ++ cmd ++ ", args: " ++ show args)
       exitCode <- rawSystem cmd args
       case exitCode of
          ExitFailure i -> raiseIO ("command failed (exit code " ++ show i ++ ")") -- \n  " ++ concat (intersperse " " (cmd:args)))
          ExitSuccess   -> return ()

runCmdRead :: [(String,String)] -> String -> [String] -> IO (String,String)
runCmdRead extraEnv cmd args
  = do mbEnv <- buildEnv extraEnv
       (_, Just hout, Just herr, process) <- createProcess (proc cmd args){ env = mbEnv, std_out = CreatePipe, std_err = CreatePipe }
       exitCode <- waitForProcess process
       case exitCode of
          ExitFailure i -> do -- hClose hout
                              raiseIO ("command failed (exit code " ++ show i ++ ")") -- \n  " ++ concat (intersperse " " (cmd:args)))
          ExitSuccess   -> do out <- hGetContents hout
                              err <- hGetContents herr
                              -- hClose hout
                              return (out,err)


runCmdEnv :: [(String,String)] -> String -> [String] -> IO ()
runCmdEnv extraEnv cmd args
  = do mbEnv <- buildEnv extraEnv
       (_, _, _, process) <- createProcess (proc cmd args){ env = mbEnv }
       exitCode <- waitForProcess process
       case exitCode of
          ExitFailure i -> do -- hClose hout
                              raiseIO ("command failed (exit code " ++ show i ++ ")") -- \n  " ++ concat (intersperse " " (cmd:args)))
          ExitSuccess   -> return ()

buildEnv :: [(String,String)] -> IO (Maybe [(String,String)])
buildEnv extraEnv
  = if null extraEnv then return Nothing
      else do oldEnv <- getEnvironment
              let newKeys = map fst extraEnv
              return (Just (extraEnv ++ filter (\(k,_) -> not (k `elem` newKeys)) oldEnv))
#endif

-- | Compare two file modification times (uses 0 for non-existing files)
fileTimeCompare :: FilePath -> FilePath -> IO Ordering
fileTimeCompare fname1 fname2
  = do time1 <- getFileTime fname1
       time2 <- getFileTime fname2
       return (compare time1 time2)


maxFileTime :: FileTime -> FileTime -> FileTime
maxFileTime t1 t2
  = if (t1 >= t2) then t1 else t2

maxFileTimes :: [FileTime] -> FileTime
maxFileTimes times
  = foldr maxFileTime fileTime0 times

#ifdef KOKA_WEB
doesFileExistAndNotEmpty :: FilePath -> IO Bool
doesFileExistAndNotEmpty fpath
  = do exist <- js_doesFileExist fpath
       if exist
         then do sz <- js_getFileSize fpath
                 return (sz > 0)
         else return False
#else
doesFileExistAndNotEmpty :: FilePath -> IO Bool
doesFileExistAndNotEmpty fpath
  = do exist <- doesFileExist fpath
       if exist
         then do fsize <- getFileSize fpath
                 return (fsize > 0)
         else return False
{-
  = do mbContent <- readTextFile fpath
       case mbContent of
         Nothing      -> return False
         Just content -> return (not (null content))
-}
#endif

#ifdef KOKA_WEB
readTextFile :: FilePath -> IO (Maybe String)
readTextFile fpath
  = do result <- js_vfsReadFile (toJSString fpath)
       if isNull result || isUndefined result
         then return Nothing
         else return (Just (fromJSString result))
#else
readTextFile :: FilePath -> IO (Maybe String)
readTextFile fpath
  = B.exCatch (do content <- readFile fpath
                  return (if null content then Just content else (seq (last content) $ Just content)))
              (\exn -> -- trace ("reading file " ++ fpath ++ " exception: " ++ exn)
                   return Nothing)
#endif

#ifdef KOKA_WEB
writeTextFile :: FilePath -> String -> IO ()
writeTextFile fpath content
  = js_vfsWriteFile (toJSString fpath) (toJSString content)
#else
writeTextFile :: FilePath -> String -> IO ()
writeTextFile fpath content
  = writeFile fpath content
#endif

#ifdef KOKA_WEB
copyTextFile :: FilePath -> FilePath -> IO ()
copyTextFile src dest
  = if src == dest then return ()
    else do mbContent <- readTextFile src
            case mbContent of
              Just content -> writeTextFile dest content
              Nothing      -> error ("could not copy file " ++ show src ++ " to " ++ show dest)

copyTextFileWith :: FilePath -> FilePath -> (String -> String) -> IO ()
copyTextFileWith src dest transform
  = if src == dest then return ()
    else do mbContent <- readTextFile src
            case mbContent of
              Just content -> writeTextFile dest (transform content)
              Nothing      -> error ("could not copy file " ++ show src ++ " to " ++ show dest)
#else
copyTextFile :: FilePath -> FilePath -> IO ()
copyTextFile src dest
  = copyTextFileWith src dest id
  {-
  = if (src == dest)
     then return ()
     else catchIO (do createDirectoryIfMissing True (dirname dest)
                      copyFileWithMetadata src dest)  -- do not use as the source may come from a (readonly) admin permission and should got to user permission
            (error ("could not copy file " ++ show src ++ " to " ++ show dest)) -}

copyTextFileWith :: FilePath -> FilePath -> (String -> String) -> IO ()
copyTextFileWith src dest transform
  = if (src == dest)
     then return ()
     else catchIO (do createDirectoryIfMissing True (dirname dest)
                      ftime   <- getFileTime src
                      content <- readFile src
                      writeFile dest (transform content)
                      setFileTime dest ftime)
            (error ("could not copy file " ++ show src ++ " to " ++ show dest))
#endif

#ifdef KOKA_WEB
copyBinaryFile :: FilePath -> FilePath -> IO ()
copyBinaryFile src dest = copyTextFile src dest  -- no binary distinction on JS
#else
copyBinaryFile :: FilePath -> FilePath -> IO ()
copyBinaryFile src dest
  = if (src == dest)
     then return ()
     else catchIO (
            -- do not use as the source may come from a (readonly) admin permission and should got to user permission
            -- B.copyBinaryFile src dest) (\_ -> error ("could not copy file " ++ show src ++ " to " ++ show dest))
             do createDirectoryIfMissing True (dirname dest)
                ftime <- getFileTime src
                withBinaryFile src ReadMode $ \hsrc ->
                  withBinaryFile dest WriteMode $ \hdest ->
                    do content <- hGetContents hsrc
                       hPutStr hdest content
                setFileTime dest ftime)
            (error ("could not copy file " ++ show src ++ " to " ++ show dest))
#endif

copyBinaryIfNewer :: Bool -> FilePath -> FilePath -> IO ()
copyBinaryIfNewer always srcName outName
  = do ord <- if (srcName == outName) then return EQ
              else if always then return GT
              else fileTimeCompare srcName outName
       if (ord == GT)
        then do copyBinaryFile srcName outName
        else do -- putStrLn $ "no copy for: " ++ srcName ++ " to " ++ outName
                return ()

copyTextIfNewer :: Bool -> FilePath -> FilePath -> IO ()
copyTextIfNewer always srcName outName
  = do ord <- if (srcName == outName) then return EQ
              else if always then return GT
              else fileTimeCompare srcName outName
       if (ord == GT)
        then do copyTextFile srcName outName
        else do return ()

copyTextIfNewerWith :: Bool -> FilePath -> FilePath -> (String -> String) -> IO ()
copyTextIfNewerWith always srcName outName transform
  = do ord <- if (srcName == outName) then return EQ
              else if always then return GT
              else fileTimeCompare srcName outName
       if (ord == GT)
        then do copyTextFileWith srcName outName transform
        else do return ()

#ifdef KOKA_WEB
removeFileIfExists :: FilePath -> IO ()
removeFileIfExists fname = js_vfsRemoveFile (toJSString fname)
#else
removeFileIfExists :: FilePath -> IO ()
removeFileIfExists fname
  = B.exCatch (removeFile fname)
              (\exn -> return ())
#endif

#ifdef KOKA_WEB
getProgramPath :: IO FilePath
getProgramPath = return "/koka"
#else
getProgramPath :: IO FilePath
getProgramPath = getExecutablePath
#endif

commonPathPrefix :: FilePath -> FilePath -> FilePath
commonPathPrefix s1 s2
  = joinPaths $ map fst $ takeWhile (\(c,d) -> c == d) $ zip (splitPath s1) (splitPath s2)


relativeToPath :: FilePath -> FilePath -> FilePath
relativeToPath prefix path
  = case mbRelativeToPath prefix path of
      Just relpath -> relpath
      Nothing      -> path

mbRelativeToPath :: FilePath -> FilePath -> Maybe FilePath
mbRelativeToPath "" path = Just path
mbRelativeToPath prefix path
  = let prefixes = splitPath prefix
        paths    = splitPath path
    in if isPrefixOf prefixes paths then Just (joinPaths (drop (length prefixes) paths)) else Nothing




-- | Is a path absolute?
isAbsolute :: FilePath -> Bool
isAbsolute fpath
  = case fpath of
      (_:':':c:_) -> isPathSep c
      (c:_)       -> isPathSep c
      _           -> False


-- | Find a maximal prefix path given a path and list of root paths. Returns the root path and relative path.
findMaximalPrefixPath :: [FilePath] -> FilePath -> Maybe (FilePath,FilePath)
findMaximalPrefixPath roots p
  = let rels = concatMap (\r -> case mbRelativeToPath r p of
                                  Just rel -> [(r,rel)]
                                  _        -> []) roots
    in case rels of
      [] -> Nothing
      xs -> Just (maximumBy (\(root1,_) (root2,_) -> compare root1 root2) xs)

-- | Get the maximal relative path
getMaximalPrefixPath :: [FilePath] -> FilePath -> (FilePath,FilePath)
getMaximalPrefixPath roots p
  = case findMaximalPrefixPath roots p of
      Nothing   -> ("",p)
      Just just -> just

{-

-- | Find a maximal prefix given a string and list of prefixes. Returns the prefix and its length.
findMaximalPrefix :: [String] -> String -> Maybe (Int,String)
findMaximalPrefix xs s
  = findMaximal (\x -> if startsWith s x then Just (length x) else Nothing) xs

findMaximal :: (a -> Maybe Int) -> [a] -> Maybe (Int,a)
findMaximal f xs
  = normalize Nothing xs
  where
    normalize res []     = res
    normalize res (x:xs) = case (f x) of
                        Just n  -> case res of
                                     Just (m,y)  | m >= n -> normalize res xs
                                     _           -> normalize (Just (n,x)) xs
                        Nothing -> normalize res xs

-}

---------------------------------------------------------------
-- file searching
----------------------------------------------------------------

searchPaths :: [FilePath] -> [String] -> String -> IO (Maybe (FilePath))
searchPaths path exts name
  = searchPathsSuffixes path exts [] name

searchPathsSuffixes :: [FilePath] -> [String] -> [String] -> String -> IO (Maybe (FilePath))
searchPathsSuffixes paths exts suffixes name
  = fmap (fmap (\(root,name) -> joinPath root name)) (searchPathsEx paths (filter (not.null) exts) suffixes name)

#ifdef KOKA_WEB
searchPathsCanonical :: FilePath -> [FilePath] -> [String] -> [String] -> String -> IO (Maybe (FilePath,FilePath))
searchPathsCanonical relativeDir paths exts suffixes name
  = do let searchPaths = if isAbsolute name then [""]
                         else if null relativeDir then paths
                         else (normalize relativeDir : paths)
       search (concatMap (\dir -> map (\n -> (dir,n)) nameext) searchPaths)
  where
    search [] = return Nothing
    search ((dir,fname):xs)
      = do let fullName = joinPath dir fname
           exist <- js_doesFileExist fullName
           if exist
             then return $ Just $! getMaximalPrefixPath paths (normalize fullName)
             else search xs
    nameext
      = concatMap (\fname -> fname : map (fname++) exts) $
        map (\suffix -> (notext nname) ++ suffix ++ (extname nname)) ("" : suffixes)
    nname
      = joinPaths $ dropWhile (==".") $ splitPath name

searchPathsEx :: [FilePath] -> [String] -> [String] -> String -> IO (Maybe (FilePath,FilePath))
searchPathsEx path exts suffixes name
  = search (concatMap (\dir -> map (\n -> (dir,n)) nameext) ("":path))
  where
    search [] = return Nothing
    search ((dir,fname):xs)
      = do let fullName = joinPath dir fname
           exist <- js_doesFileExist fullName
           if exist
             then return (Just (dir,fname))
             else search xs
    nameext
      = concatMap (\fname -> fname : map (fname++) exts) $
        map (\suffix -> (notext nname) ++ suffix ++ (extname nname)) ("" : suffixes)
    nname
      = joinPaths $ dropWhile (==".") $ splitPath name
#else
searchPathsCanonical :: FilePath -> [FilePath] -> [String] -> [String] -> String -> IO (Maybe (FilePath,FilePath))
searchPathsCanonical relativeDir paths exts suffixes name
  = do searchPaths <- if isAbsolute name then return [""]
                        else if (null relativeDir) then return paths
                        else do relDir <- realPath relativeDir
                                return (relDir : paths)
       search (concatMap (\dir -> map (\n -> (dir,n)) nameext) searchPaths)
  where
    search [] = return Nothing  -- notfound envname nameext path
    search ((dir,fname):xs)
      = do{ let fullName = joinPath dir fname
          -- ; trace ("search: " ++ fullName) $ return ()
          ; exist <- doesFileExist fullName
          ; if exist
             then do rpath <- realPath fullName
                     -- trace ("search found: " ++ fullName ++ ", in (" ++ dir ++ "," ++ fname ++ ") ,real path: " ++ rpath) $
                     return $ Just $! getMaximalPrefixPath paths rpath   -- not to the relativeDir!
             else search xs
          }

    nameext
      = concatMap (\fname -> fname : map (fname++) exts) $
        map (\suffix -> (notext nname) ++ suffix ++ (extname nname)) ("" : suffixes)

    nname
      = joinPaths $ dropWhile (==".") $ splitPath name

searchPathsEx :: [FilePath] -> [String] -> [String] -> String -> IO (Maybe (FilePath,FilePath))
searchPathsEx path exts suffixes name
  = -- trace ("search " ++ name ++ " in " ++ show path) $
    search (concatMap (\dir -> map (\n -> (dir,n)) nameext) ("":path))
  where
    search [] = return Nothing  -- notfound envname nameext path
    search ((dir,fname):xs)
      = do{ let fullName = joinPath dir fname
          ; exist <- doesFileExist fullName
          ; if exist
             then return (Just (dir,fname))
             else search xs
          }
    nameext
      = concatMap (\fname -> fname : map (fname++) exts) $
        map (\suffix -> (notext nname) ++ suffix ++ (extname nname)) ("" : suffixes)

    nname
      = joinPaths $ dropWhile (==".") $ splitPath name
#endif


-- | Make a file path relative to a set of given paths: return the (maximal) root and stem
-- if it is not relative to the paths, return dirname/notdir
makeRelativeToPaths :: [FilePath] -> FilePath -> (FilePath,FilePath)
makeRelativeToPaths paths fname
  = case findMaximalPrefixPath paths fname of
      Just (root,rpath) -> (root,rpath)
      _                 -> (dirname fname, notdir fname)



#ifdef KOKA_WEB
getEnvPaths :: String -> IO [FilePath]
getEnvPaths _ = return []

getEnvVar :: String -> IO String
getEnvVar _ = return ""
#else
getEnvPaths :: String -> IO [FilePath]
getEnvPaths name
  = do{ xs <- getEnvVar name
      ; return (undelimPaths xs)
      }
  `catchIO` \err -> return []

getEnvVar :: String -> IO String
getEnvVar name
  = do env <- getEnvironment
       case lookup (map toLower name) (map (\(k,v) -> (map toLower k,v)) env) of
         Just val -> return val
         Nothing  -> return ""
#endif

#ifdef KOKA_WEB
realPath :: FilePath -> IO FilePath
realPath fpath = return (normalize fpath)
#else
realPath :: FilePath -> IO FilePath
realPath fpath
  = do fullpath <- if onWindows && fpath `startsWith` "//"
                     then return fpath              -- on windows leave network paths alone as Haskell's `normalise` removes double `//` :-(
                     else canonicalizePath fpath
       return (normalize fullpath)
#endif

#ifdef KOKA_WEB
searchProgram :: FilePath -> IO (Maybe FilePath)
searchProgram _ = return Nothing
#else
searchProgram :: FilePath -> IO (Maybe FilePath)
searchProgram ""
  = return Nothing
searchProgram fname | isAbsolute fname || fname `startsWith` "."
  = do exist <- doesFileExist fname
       if exist
         then return (Just fname)
         else return Nothing
searchProgram fname
  = do paths  <- getEnvPaths "PATH"
       searchPaths paths [exeExtension] fname
#endif


{-
splitPath :: String -> [String]
splitPath xs
  = normalize [] "" xs
  where
    normalize ps "" (c:':':cs)
      = normalize ps (':':c:[]) cs

    normalize ps p xs
      = case xs of
          []             -> if (null p)
                             then reverse ps
                             else reverse (reverse p:ps)
          (';':cs)       -> normalize (reverse p:ps) "" cs
          (':':cs)       -> normalize (reverse p:ps) "" cs
          (c:cs)         -> normalize ps (c:p) cs
-}

#ifdef KOKA_WEB
-- JS VFS FFI declarations

foreign import javascript unsafe "((p) => { return globalThis.kokaVFS.fileExists(p); })"
  js_vfsFileExistsRaw :: JSVal -> IO Bool

foreign import javascript unsafe "((p) => { return globalThis.kokaVFS.fileSize(p); })"
  js_vfsFileSizeRaw :: JSVal -> IO Int

foreign import javascript unsafe "((p,c) => { globalThis.kokaVFS.writeFile(p,c); })"
  js_vfsWriteFileRaw :: JSVal -> JSVal -> IO ()

foreign import javascript unsafe "((p) => { globalThis.kokaVFS.removeFile(p); })"
  js_vfsRemoveFileRaw :: JSVal -> IO ()

foreign import javascript interruptible "((p,cont) => { var r = globalThis.kokaVFS.readFile(p); if (r && typeof r.then === 'function') { r.then(function(v){ cont(v); }); } else { cont(r); } })"
  js_vfsReadFileRaw :: JSVal -> IO JSVal

-- Wrapper functions that handle String <-> JSVal conversion
js_doesFileExist :: FilePath -> IO Bool
js_doesFileExist fpath = js_vfsFileExistsRaw (toJSString fpath)

js_getFileSize :: FilePath -> IO Int
js_getFileSize fpath = js_vfsFileSizeRaw (toJSString fpath)

js_vfsReadFile :: JSVal -> IO JSVal
js_vfsReadFile = js_vfsReadFileRaw

js_vfsWriteFile :: JSVal -> JSVal -> IO ()
js_vfsWriteFile = js_vfsWriteFileRaw

js_vfsRemoveFile :: JSVal -> IO ()
js_vfsRemoveFile jsPath = js_vfsRemoveFileRaw jsPath
#endif
