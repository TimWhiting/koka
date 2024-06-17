------------------------------------------------------------------------------
-- Copyright 2023, Tim Whiting, Fredrik Wieczerkowski
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- The LSP handler that provides hover tooltips
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}

module LanguageServer.Handler.Hover (hoverHandler, formatRangeInfoHover) where

import Control.Lens ((^.))
import Control.Monad.IO.Class (liftIO)
import qualified Data.Text as T
import qualified Data.Set as S
import Data.List (intercalate,find)
import Data.Char(isSpace)
import Data.Maybe (fromJust)
import Data.Time (diffUTCTime)
import Data.Time.Clock (getCurrentTime)
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Lens as J
import qualified Language.LSP.Protocol.Message as J
import Language.LSP.Server (Handlers, sendNotification, requestHandler)

import Common.Range as R
import Common.Range (showFullRange)
import Common.Name (nameNil, ModuleName)
import Common.ColorScheme (ColorScheme (colorNameQual, colorSource), Color (Gray))
import Compile.Module (modRangeMap, modLexemes, Module (modSourcePath, modCoreUnopt))
import Compile.Options (Flags, colorSchemeFromFlags, prettyEnvFromFlags)
import Compile.BuildMonad(runBuild)
import Compile.BuildContext(buildcTypeCheck)
import Kind.Kind(isKindEffect,isKindHandled,isKindHandled1,isKindLabel)
import Kind.Pretty (prettyKind)
import Kind.ImportMap (importsEmpty, ImportMap)
import Type.Pretty (ppScheme, defaultEnv, Env(..), ppName, keyword)
import Type.Type (Name)
import Lib.PPrint
    ( Pretty(..), Doc, text, (<+>), color, empty, (<.>), (<->), vcat)
import Syntax.RangeMap
    ( NameInfo(..),
      RangeInfo(..),
      rangeMapFindAt,
      NameInfo(..),
      RangeInfo(..),
      rangeMapFindAt )
import Syntax.Colorize ( removeComment, removeComment )
import Syntax.Pretty (ppSyntaxExpr, ppSyntaxDef, ppSyntaxExtern, ppLit)
import Core.FlowAnalysis.Demand.Syntax (runEvalQueryFromRangeSource)
import Core.FlowAnalysis.Demand.DemandAnalysis (AnalysisKind (..))
import LanguageServer.Conversions (fromLspPos, toLspRange)
import LanguageServer.Monad
import LanguageServer.Handler.Pretty (ppComment, asKokaCode)
import Debug.Trace (trace)
import Core.Pretty (prettyCore)
import Common.Syntax (Target(..), CTarget (..))
import System.Directory (createDirectoryIfMissing)

toAbValueText (env, (fns, defs, externs, lits, constrs, topTypes)) =
  let closureText = if null fns then "" else intercalate "\n" (map (\d -> "```koka\n" ++ show (ppSyntaxExpr d) ++ "\n```") fns)
      litsText = if null lits then "" else intercalate "\n" (map ppLit lits)
      defsText = if null defs then "" else "\n\nDefinitions:\n\n" <> intercalate "\n\n " (map (\d -> "```koka\n" ++ show (ppSyntaxDef d) ++ "\n```") defs)
      externsText = if null externs then "" else "\n\nExterns:\n\n" <> intercalate "\n\n " (map (\d -> "```koka\n" ++ show (ppSyntaxExtern d) ++ "\n```") externs)
      constrsText = if null constrs then "" else "\n\nConstructors:\n\n" <> intercalate "\n\n " (map (\d -> "```koka\n" ++ d ++ "\n```") constrs)
      topTypesText = if null topTypes then "" else "\n\nTop-level types:\n\n" <> unwords (map (show . ppScheme defaultEnv) (S.toList topTypes))
      resText = closureText <> litsText <> defsText <> externsText <> constrsText <> topTypesText
      hc =
        ("\n\nIn Context: " <> show env <> "\n\nEvaluates to:\n\n" <> (if null resText then "?" else resText))
  in T.pack hc

-- Handles hover requests
hoverHandler :: Handlers LSM
hoverHandler
  = requestHandler J.SMethod_TextDocumentHover $ \req responder ->
    do  let J.HoverParams doc pos0 _ = req ^. J.params
            uri  = J.toNormalizedUri (doc ^. J.uri)

            done :: LSM ()
            done = responder $ Right $ J.InR J.Null

            liftMaybe :: LSM (Maybe a) -> (a -> LSM ()) -> LSM ()
            liftMaybe action next = do res <- action
                                       maybe done next res

        pos <- liftIO $ fromLspPos uri pos0
        trace ("hover: lookup: " ++ show uri) $ return ()
        liftMaybe (lookupModuleName uri) $ \(fpath,modname) ->
          -- trace ("hover: found: " ++ show modname) $
           liftMaybe (lookupRangeMap modname) $ \(rmap,lexemes) ->
            -- trace ("hover: found rangemap: " ) $
             liftMaybe (return (rangeMapFindAt lexemes pos rmap)) $ \(rng,rngInfo) ->
              -- trace ("hover: found rng info: " ++ show rngInfo) $
              do penv <- getPrettyEnvFor modname
                 mods <- lookupModulePaths
                 mod <- lookupModule modname
                 buildContext <- getBuildContext
                 term <- getTerminal
                 flags <- getFlags
                 let doc = formatRangeInfoHover penv mods rngInfo
                 tstart <- liftIO getCurrentTime
                 liftIO $ createDirectoryIfMissing True "scratch/debug"
                 liftIO $ writeFile "scratch/debug/hover.kk" $ show (prettyCore defaultEnv (C CDefault) [] (fromJust $ modCoreUnopt (fromJust mod)))
                 !res <- liftIO $ trace ("Running eval for position " ++ show pos) $ 
                            runEvalQueryFromRangeSource 
                              buildContext (\bc mod -> (runBuild term flags (buildcTypeCheck [mod] bc))) (rng, rngInfo) 
                              (fromJust mod) BasicEnvs 1
                 tend <- liftIO getCurrentTime
                 case res of
                    (!x:xs, !newBuildContext) -> do
                      updateBuildContext newBuildContext
                      markdown <- prettyMarkdown doc
                      let rsp = J.Hover (J.InL (J.mkMarkdown (markdown <>
                                                          T.intercalate "\n\n" (map toAbValueText (x:xs)) <>
                                                          "\n\n" <> T.pack (show $ diffUTCTime tend tstart))))
                                                          (Just (toLspRange rng))
                      -- trace ("hover markdown:\n" ++ show markdown) $
                      responder $ Right $ J.InL rsp
                    _ -> do
                      markdown <- prettyMarkdown doc
                      let rsp = J.Hover (J.InL (J.mkMarkdown markdown)) (Just (toLspRange rng))
                      -- trace ("hover markdown:\n" ++ show markdown) $
                      responder $ Right $ J.InL rsp


-- Pretty-prints type/kind information to a hover tooltip given a type pretty environment, color scheme
formatRangeInfoHover :: Env -> [(ModuleName,FilePath)] -> RangeInfo -> Doc
formatRangeInfoHover env mods rinfo
  = let kw = keyword env
    in case rinfo of
      Decl s name mname mbType -> asKokaCode (kw s <+> pretty name <.>
                                              case mbType of
                                                Just tp -> text " :" <+> ppScheme env tp
                                                Nothing -> empty)
      Block s             -> asKokaCode (kw s)
      Error doc           -> text "error:" <+> doc
      Warning doc         -> text "warning:" <+> doc
      Implicits fdoc      -> text "implicits:" <+> fdoc False  -- should not occur

      Id qname info docs isdef ->
        let namedoc   = ppName env qname
            signature = case info of
                          NIValue sort tp doc _  -> (if null sort then empty else kw sort) <+> namedoc <+> text ":" <+> ppScheme env tp
                          NICon tp doc      -> kw "con" <+> namedoc <+> text ":" <+> ppScheme env tp
                          NITypeCon k doc   -> (if isKindEffect k || isKindHandled k || isKindLabel k
                                                  then kw "effect"
                                                  else if isKindHandled1 k
                                                    then kw "linear effect"
                                                    else kw "type")
                                                <+> namedoc <+> text "::" <+> prettyKind (colors env) k
                          NITypeVar k       -> kw "type" <+> namedoc <+> text "::" <+> prettyKind (colors env) k
                          NIModule -> kw "module" <+> namedoc <.>
                                      (case find (\(modname,fpath) -> modname == qname) mods of
                                            Just (modname,fpath) -> text (" (at \"" ++ fpath ++ "\")")
                                            Nothing -> empty
                                        )
                          NIKind -> kw "kind" <+> namedoc
            comment = case info of
                        NIValue _ tp doc _ -> ppComment doc
                        NICon tp doc       -> ppComment doc
                        NITypeCon k doc    -> ppComment doc
                        _                  -> empty
        in asKokaCode (if null docs then signature else signature <.> text "  " <-> color Gray (vcat docs))
          <.> comment
