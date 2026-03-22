{-# OPTIONS -cpp #-}
------------------------------------------------------------------------------
-- Copyright 2024, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Main entry point for the browser-based playground.
    Registers a compilation callback on globalThis that the JS frontend calls.
-}
-----------------------------------------------------------------------------
module Main where

#ifdef KOKA_WEB

import GHC.JS.Prim           ( JSVal, toJSString, fromJSString )
import GHC.JS.Foreign.Callback ( Callback, asyncCallback1, asyncCallback2 )

import Control.Monad          ( when )
import Data.IORef             ( IORef, newIORef, readIORef, modifyIORef )
import Data.List              ( intersperse )

import Lib.PPrint
import Lib.Printer

import Common.Name
import Common.Error
import Common.ColorScheme
import Common.Range           ( BString, stringToBString )

import Compile.Options        ( playgroundFlags, playgroundOptions, Flags(..), Terminal(..) )
import Compile.BuildContext
import Compile.Build          ( virtualMount )

-- | Main entry point: registers the compiler callback and keeps the runtime alive.
main :: IO ()
main = do
  compileCb <- asyncCallback2 compileHandler
  js_setCompiler compileCb
  js_keepAlive

-- | Handle a compile request from JavaScript.
-- Takes a module name and source text (as JSVal strings),
-- compiles the source, and sets the result on globalThis.kokaResult.
compileHandler :: JSVal -> JSVal -> IO ()
compileHandler jsModName jsSource = do
  let modName = fromJSString jsModName
      source  = fromJSString jsSource
  result <- compileToJS modName source
  js_setResult (toJSString result)

-- | Compile a Koka source string to JavaScript.
-- Returns a JSON string with either the generated JS code or error messages.
compileToJS :: String -> String -> IO String
compileToJS moduleName sourceText = do
  errRef <- newIORef []
  v <- js_getVerbose
  let flags = playgroundFlags{ verbose = v }
      term  = playgroundTerminal errRef
      sourcePath = virtualMount ++ "/" ++ moduleName ++ ".kk"
      content    = stringToBString sourceText
  (mbResult, _) <- runBuildIO term flags False $ do
    let buildc0 = buildcEmpty flags
    withVirtualModule sourcePath content buildc0 $ \mainModName buildc1 ->
      do -- Build: lex, parse, type check, optimize, codegen
         buildc2 <- buildcBuildEx False [] [] buildc1
         buildcThrowOnError buildc2
         return (buildc2, ())
  errs <- readIORef errRef
  case mbResult of
    Just _  -> return "{\"success\": true}"
    Nothing -> return ("{\"success\": false, \"errors\": " ++ show (reverse errs) ++ "}")

-- | A terminal that collects errors and sends phase/trace messages to JS.
playgroundTerminal :: IORef [String] -> Terminal
playgroundTerminal errRef
  = Terminal (\err -> modifyIORef errRef (show err :))  -- error handler
             (\msg -> js_logCompiler (toJSString msg))  -- trace
             (\_ -> return ())                           -- progress
             (\doc -> js_logCompiler (toJSString (show doc)))  -- phase info
             (\doc -> js_logCompiler (toJSString (show doc)))  -- general info

-- JS FFI: register the compiler callback on globalThis
foreign import javascript unsafe "h$kokaSetCompiler"
  js_setCompiler :: Callback (JSVal -> JSVal -> IO ()) -> IO ()

-- JS FFI: set the compilation result on globalThis
foreign import javascript unsafe "h$kokaSetResult"
  js_setResult :: JSVal -> IO ()

-- JS FFI: get verbosity level from JS
foreign import javascript unsafe "h$kokaGetVerbose"
  js_getVerbose :: IO Int

-- JS FFI: send compiler log message to JS
foreign import javascript unsafe "h$kokaLogCompiler"
  js_logCompiler :: JSVal -> IO ()

-- JS FFI: keep the Haskell runtime alive (block forever)
-- The runtime needs to stay alive to handle callbacks.
foreign import javascript safe "h$kokaKeepAlive"
  js_keepAlive :: IO ()

#elif defined(KOKA_WASM)

-- WASM build: compile from stdin or command-line argument, write to stdout.
-- Uses WASI filesystem for VFS operations.

import Control.Monad          ( when )
import Data.IORef             ( IORef, newIORef, readIORef, modifyIORef )
import System.IO              ( hPutStrLn, stderr, hFlush, stdout )
import System.Environment     ( getArgs )

import Lib.PPrint
import Lib.Printer

import Common.Name
import Common.Error
import Common.ColorScheme
import Common.Range           ( BString, stringToBString )

import Compile.Options        ( playgroundFlags, Flags(..), Terminal(..) )
import Compile.BuildContext
import Compile.Build          ( virtualMount )

main :: IO ()
main = do
  args <- getArgs
  case args of
    [moduleName, sourceText] -> do
      result <- compileToJS moduleName sourceText
      putStrLn result
      hFlush stdout
    [moduleName] -> do
      sourceText <- getContents
      result <- compileToJS moduleName sourceText
      putStrLn result
      hFlush stdout
    _ -> do
      hPutStrLn stderr "Usage: koka-playground <module-name> [source-text]"
      hPutStrLn stderr "  Or pipe source via stdin: echo 'module main ...' | koka-playground main"

compileToJS :: String -> String -> IO String
compileToJS moduleName sourceText = do
  errRef <- newIORef []
  let flags = playgroundFlags{ verbose = 0 }
      term  = Terminal (\err -> modifyIORef errRef (show err :))
                       (\_ -> return ())
                       (\_ -> return ())
                       (\_ -> return ())
                       (\_ -> return ())
      sourcePath = virtualMount ++ "/" ++ moduleName ++ ".kk"
      content    = stringToBString sourceText
  (mbResult, _) <- runBuildIO term flags False $ do
    let buildc0 = buildcEmpty flags
    withVirtualModule sourcePath content buildc0 $ \mainModName buildc1 ->
      do buildc2 <- buildcBuildEx False [] [] buildc1
         buildcThrowOnError buildc2
         return (buildc2, ())
  errs <- readIORef errRef
  case mbResult of
    Just _  -> return "{\"success\": true}"
    Nothing -> return ("{\"success\": false, \"errors\": " ++ show (reverse errs) ++ "}")

#else

-- Native build: this executable is not useful outside the JS/WASM backend.
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  hPutStrLn stderr "koka-playground is only available when built with the GHC JavaScript or WASM backend."
  hPutStrLn stderr "Build with: cabal build --with-compiler=javascript-unknown-ghcjs-ghc koka-playground"
  hPutStrLn stderr "       or:  cabal build --with-compiler=wasm32-wasi-ghc koka-playground"

#endif
