-----------------------------------------------------------------------------
-- The LSP handler that provides hover tooltips
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

module LanguageServer.Handler.Hover (hoverHandler, formatRangeInfoHover) where

import Compiler.Module (loadedModule, modRangeMap, Loaded (loadedModules), Module (modPath, modSourcePath))
import Control.Lens ((^.))
import qualified Data.Map as M
import qualified Data.Text as T
import Language.LSP.Server (Handlers, sendNotification, requestHandler)
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Lens as J
import LanguageServer.Conversions (fromLspPos, toLspRange)
import LanguageServer.Monad (LSM, getLoaded, getLoadedModule, putLoaded)
import Lib.PPrint (Pretty (..))
import Syntax.RangeMap (NameInfo (..), RangeInfo (..), rangeMapFindAt)
import qualified Language.LSP.Protocol.Message as J
import Core.DemandAnalysis (runEvalQueryFromRangeSource)
import Debug.Trace (trace)
import Common.Range (showFullRange)
import LanguageServer.Handler.TextDocument (getCompile)
import Core.StaticContext (showSyntax, showLit, showSyntaxDef)
import qualified Data.Set as S
import Type.Pretty (ppType, defaultEnv)
import Data.List (intercalate)

toAbValueText (env, (fns, defs, lits, constrs, topTypes, errs)) =
  let closureText = if null fns then "" else intercalate "\n" (map (\d -> "```koka\n" ++  showSyntax 0 d ++ "\n```") fns)
      litsText = if null lits then "" else intercalate "\n" (map showLit lits)
      defsText = if null defs then "" else "\n\nDefinitions:\n\n" <> intercalate "\n\n " (map (\d -> "```koka\n" ++ showSyntaxDef 0 d ++ "\n```") defs)
      constrsText = if null constrs then "" else "\n\nConstructors:\n\n" <> intercalate "\n\n " (map (\d -> "```koka\n" ++ d ++ "\n```") constrs)
      topTypesText = if null topTypes then "" else "\n\nTop-level types:\n\n" <> unwords (map (show . ppType defaultEnv) (S.toList topTypes))
      resText = closureText <> litsText <> defsText <> constrsText <> topTypesText
      errText = if null errs then "" else "\n\nIncomplete Evaluation: Stuck at errors:\n\n" <> intercalate "\n\n" (S.toList errs)
      hc =
        ("\n\nIn Context: " <> show env <> "\n\nEvaluates to:\n\n" <> (if (not . null) errText then errText else if null resText then "(unknown error)" else resText))
  in hc

hoverHandler :: Handlers LSM
hoverHandler = requestHandler J.SMethod_TextDocumentHover $ \req responder -> do
  let J.HoverParams doc pos _ = req ^. J.params
      uri = doc ^. J.uri
  allLoaded <- getLoaded
  loaded <- getLoadedModule uri
  compile <- getCompile
  let rsp = do
        l <- loaded
        allMods <- allLoaded
        rmap <- modRangeMap l
        (r, rinfo) <- rangeMapFindAt (fromLspPos uri pos) rmap
        let (xs, newLoaded) = trace ("Running eval for position " ++ show (fromLspPos uri pos)) $ runEvalQueryFromRangeSource allMods compile (r, rinfo) l
            hc = J.InL $ J.mkMarkdown $ T.pack $ formatRangeInfoHover rinfo <> intercalate "\n\n" (map toAbValueText xs)
        -- TODO: Parse module, get tokens of the lambda and colorize it, see colorize for a start 
        -- (just need to use AnsiString printer and working from a string/part of file rather than a whole file)

            hover = J.Hover hc $ Just $ toLspRange r
        return (hover, newLoaded)
  case rsp of
    Nothing -> responder $ Right $ J.InR J.Null
    Just (rsp, ld) -> do
      putLoaded ld
      responder $ Right $ J.InL rsp

-- Pretty-prints type/kind information to a hover tooltip
formatRangeInfoHover :: RangeInfo -> String
formatRangeInfoHover rinfo = case rinfo of
  Id qname info isdef ->
    show (pretty qname) ++ " : " ++ case info of
      NIValue tp -> show $ pretty tp
      NICon tp -> show $ pretty tp
      NITypeCon k -> show $ pretty k
      NITypeVar k -> show $ pretty k
      NIModule -> "module"
      NIKind -> "kind"
  Decl s name mname -> s ++ " " ++ show (pretty name)
  Block s -> s
  Error doc -> "Error: " ++ show doc
  Warning doc -> "Warning: " ++ show doc
