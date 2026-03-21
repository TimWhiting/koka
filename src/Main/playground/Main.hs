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
  let flags = playgroundFlags
      term  = silentTerminal
      sourcePath = virtualMount ++ "/" ++ moduleName ++ ".kk"
      content    = stringToBString sourceText
  (mbResult, _) <- runBuildIO term flags False $ do
    let buildc0 = buildcEmpty flags
    withVirtualModule sourcePath content buildc0 $ \mainModName buildc1 ->
      do -- Build: lex, parse, type check, optimize, codegen
         buildc2 <- buildcBuildEx False [] [] buildc1
         buildcThrowOnError buildc2
         return ()
  case mbResult of
    Just _  -> return "{\"success\": true}"
    Nothing -> return "{\"success\": false}"

-- | A terminal that discards all output.
-- Errors are collected in the Build monad's error state.
silentTerminal :: Terminal
silentTerminal
  = Terminal (\_ -> return ())     -- error handler (errors collected in Build monad)
             (\_ -> return ())     -- trace
             (\_ -> return ())     -- progress
             (\_ -> return ())     -- phase info
             (\_ -> return ())     -- general info

-- JS FFI: register the compiler callback on globalThis
foreign import javascript unsafe "((cb) => { globalThis.kokaCompile = cb; })"
  js_setCompiler :: Callback (JSVal -> JSVal -> IO ()) -> IO ()

-- JS FFI: set the compilation result on globalThis
foreign import javascript unsafe "((s) => { globalThis.kokaResult = s; })"
  js_setResult :: JSVal -> IO ()

-- JS FFI: keep the Haskell runtime alive (block forever)
-- The runtime needs to stay alive to handle callbacks.
foreign import javascript interruptible "((cont) => { /* never call cont — keep runtime alive */ })"
  js_keepAlive :: IO ()

#else

-- Native build: this executable is not useful outside the JS backend.
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  hPutStrLn stderr "koka-playground is only available when built with the GHC JavaScript backend."
  hPutStrLn stderr "Build with: cabal build --with-compiler=javascript-unknown-ghcjs-ghc koka-playground"

#endif
