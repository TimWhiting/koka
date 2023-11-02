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
import Core.DemandAnalysis (runEvalQueryFromRange, runEvalQueryFromRangeSource)
import Debug.Trace (trace)
import Common.Range (showFullRange)
import LanguageServer.Handler.TextDocument (getCompile)
import Syntax.Syntax (showSyntax, showLit)

hoverHandler :: Handlers LSM
hoverHandler = requestHandler J.SMethod_TextDocumentHover $ \req responder -> do
  let J.HoverParams doc pos _ = req ^. J.params
      uri = doc ^. J.uri
      normUri = J.toNormalizedUri uri
  allLoaded <- getLoaded
  loaded <- getLoadedModule uri
  compile <- getCompile
  let rsp = do
        l <- loaded
        allMods <- allLoaded
        rmap <- modRangeMap l
        (r, rinfo) <- rangeMapFindAt (fromLspPos uri pos) rmap
        let (fns, lits, newLoaded) = trace ("Running eval for position " ++ show (fromLspPos uri pos)) $ runEvalQueryFromRangeSource allMods compile (r, rinfo) l
        -- TODO: Parse module, get tokens of the lambda and colorize it, see colorize for a start 
        -- (just need to use AnsiString printer and working from a string/part of file rather than a whole file)
        let hc = J.InL $ J.mkMarkdown $ T.pack $ formatRangeInfoHover rinfo <> ("\n\nEvaluates to:\n\n" <> T.unpack (T.intercalate "\n\n" (map (T.pack . showSyntax) fns ++ map (T.pack . showLit) lits)))
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
