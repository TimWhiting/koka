------------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Main module.
-}
-----------------------------------------------------------------------------
module Main where

import System.Exit            ( exitFailure )
import Control.Monad          ( when, foldM )

import Platform.Config
import Lib.PPrint             ( Pretty(pretty), writePrettyLn, text,color, (<.>), linebreak, writeAtomicPrettyLn )
import Lib.Printer
import Common.ColorScheme
import Common.Failure         ( catchIO )
import Common.Error
import Common.Name
import Common.File            ( joinPath, getCwd )
import Compiler.Options
import Compiler.Compile       ( compileFile, CompileTarget(..), Module(..), Loaded(..), Terminal(..) )
import Core.Core              ( coreProgDefs, flattenDefGroups, defType, Def(..) )
import Interpreter.Interpret  ( interpret  )
import Kind.ImportMap         ( importsEmpty )
import Kind.Synonym           ( synonymsIsEmpty, ppSynonyms, synonymsFilter )
import Kind.Assumption        ( kgammaFilter )
import LanguageServer.Run     ( runLanguageServer )
import Type.Assumption        ( ppGamma, ppGammaHidden, gammaFilter, createNameInfoX, gammaNew )
import Type.Pretty            ( ppScheme, Env(context,importsMap) )
import System.IO (hPutStrLn, stderr)
import Data.List (intercalate)
import GHC.IO.Encoding( setLocaleEncoding, utf8 )

-- compiled entry
main      =  -- runExample
  mainArgs ""

-- ghci entry
maing     = maingg ""
maindoc   = maingg "--html"
mainjs    = maingg "--target=js"
maincs    = maingg "--target=cs"

maingg extraOptions
  = mainArgs ("-ilib -itest --verbose " ++ extraOptions)

-- hugs entry
mainh     = mainArgs "-ilib -itest --console=raw"


mainArgs args
  = do setLocaleEncoding utf8  -- set system wide utf8 regardless of locale
       (flags,flags0,mode) <- getOptions args
       let with = if (not (null (redirectOutput flags)))
                   then withFileNoColorPrinter (redirectOutput flags)
                   else if (console flags == "html")
                    then withHtmlColorPrinter
                   else if (console flags == "ansi")
                    then withColorPrinter
                    else withNoColorPrinter
       with (mainMode flags flags0 mode)
    `catchIO` \err ->
    do if ("ExitFailure" `isPrefix` err)
        then return ()
        else putStr err
       exitFailure
  where
    isPrefix s t  = (s == take (length s) t)

mainMode :: Flags -> Flags -> Mode -> ColorPrinter -> IO ()
mainMode flags flags0 mode p
  = case mode of
     ModeHelp
      -> showHelp flags p
     ModeVersion
      -> withNoColorPrinter (\monop -> showVersion flags monop)
     ModeCompiler files
      -> do
        errFiles <- foldM (\errfiles file ->
            do
              res <- compile p flags file
              if res then return errfiles
              else return (file:errfiles)
            ) [] files
        if null errFiles then return ()
        else do
          hPutStrLn stderr ("Failed to compile " ++ intercalate "," files)
          exitFailure
     ModeInteractive files
      -> interpret p flags flags0 files
     ModeLanguageServer files
      -> runLanguageServer flags files


compile :: ColorPrinter -> Flags -> FilePath -> IO Bool
compile p flags fname
  = do let exec = Executable (newName "main") ()
       cwd <- getCwd
       err <- compileFile (const Nothing) Nothing (term cwd) flags []
                (if (not (evaluate flags)) then (if library flags then Library else exec) else exec) [] fname
       case checkError err of
         Left (Errors errs)
           -> do mapM_ (\err -> putPrettyLn p (ppErrorMessage cwd (showSpan flags) cscheme err)) errs
                 -- exitFailure  -- don't fail for tests
                 return False
         Right ((Loaded gamma kgamma synonyms newtypes constructors _ imports _
                (Module modName _ _ _ _ _ _ rawProgram core _ _ _ _ modTime) _ _ _
                , _), Errors warnings)
           -> do when (not (null warnings))
                   (mapM_ (\err -> putPrettyLn p (ppErrorMessage cwd (showSpan flags) cscheme err)) warnings)
                 when (showKindSigs flags) $ do
                       putPrettyLn p (pretty (kgammaFilter modName kgamma))
                       let localSyns = synonymsFilter modName synonyms
                       when (not (synonymsIsEmpty localSyns))
                        (putPrettyLn p (ppSynonyms (prettyEnv flags modName imports) localSyns))

                 if showHiddenTypeSigs flags
                   then -- workaround since private defs aren't in gamma
                        putPrettyLn p $ ppGammaHidden (prettyEnv flags modName imports) $ gammaFilter modName $ gammaFromDefGroups $ coreProgDefs core
                   else if showTypeSigs flags
                          then putPrettyLn p $ ppGamma (prettyEnv flags modName imports) $ gammaFilter modName gamma
                          else return ()
                 return True
  where
    term cwd
      = Terminal (putErrorMessage p cwd (showSpan flags) cscheme)
                (if (verbose flags > 1) then (\msg -> writeAtomicPrettyLn p (color (colorSource cscheme) (text msg)))
                                        else (\_ -> return ()))
                 (if (verbose flags > 0) then writeAtomicPrettyLn p else (\_ -> return ()))
                 (putScheme p (prettyEnv flags nameNil importsEmpty))
                 (writeAtomicPrettyLn p)

    cscheme
      = colorSchemeFromFlags flags

    prettyEnv flags ctx imports
      = (prettyEnvFromFlags flags){ context = ctx, importsMap = imports }

gammaFromDefGroups groups = gammaNew $ map defToGammaEntry $ flattenDefGroups groups
  where
    defToGammaEntry def = (defName def, createNameInfoX (defVis def) (defName def)  (defSort def) (defNameRange def) (defType def) (defDoc def))

putScheme p env tp
  = putPrettyLn p (ppScheme env tp)

putErrorMessage p cwd endToo cscheme err
  = putPrettyLn p (ppErrorMessage cwd endToo cscheme err)

putPhase p cscheme msg
  = withColor p (colorInterpreter cscheme) (writeLn p msg)

putPrettyLn p doc
  = writeAtomicPrettyLn p (doc <.> linebreak)
