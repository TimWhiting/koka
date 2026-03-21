{-# OPTIONS -cpp #-}
------------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Configuration data (GHC JavaScript backend variant)
-}
-----------------------------------------------------------------------------
module Platform.Config where

-- by not inlining these we avoid rebuilding too many source files (since the .hi stays unchanged)
{-# NOINLINE version #-}
{-# NOINLINE buildDate #-}
{-# NOINLINE buildTime #-}

programName :: String
#if defined(KOKA_MAIN)
programName = KOKA_MAIN
#else
programName = "koka"
#endif

version :: String
#if defined(KOKA_VERSION)
version = KOKA_VERSION
#else
version = "0"
#endif

compilerBuildVariant :: String
compilerBuildVariant = "web"

compiler :: String
compiler = "ghcjs"

exeExtension   :: String
pathSep,pathDelimiter :: Char

-- platform = "js"
exeExtension  = ""
dllExtension  = ".js"
objExtension  = ".js"
libExtension  = ".js"
libPrefix     = ""
pathSep       = '/'
pathDelimiter = ':'

sourceExtension :: String
sourceExtension = ".kk"

buildDate :: String
#ifdef DATE
buildDate  = DATE
#else
buildDate  = __DATE__
#endif

buildTime :: String
buildTime  = __TIME__ ++ " " ++ __DATE__
