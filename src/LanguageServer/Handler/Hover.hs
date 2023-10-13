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
import LanguageServer.Monad (LSM, getLoaded, getLoadedModule)
import Lib.PPrint (Pretty (..))
import Syntax.RangeMap (NameInfo (..), RangeInfo (..), rangeMapFindAt)
import qualified Language.LSP.Protocol.Message as J
import Core.DemandAnalysis (runEvalQueryFromRange)
import Debug.Trace (trace)
import Common.Range (showFullRange)

hoverHandler :: Handlers LSM
hoverHandler = requestHandler J.SMethod_TextDocumentHover $ \req responder -> do
  let J.HoverParams doc pos _ = req ^. J.params
      uri = doc ^. J.uri
      normUri = J.toNormalizedUri uri
  allLoaded <- getLoaded
  loaded <- getLoadedModule uri
  let rsp = do
        l <- loaded
        allMods <- allLoaded
        rmap <- modRangeMap l
        (r, rinfo) <- rangeMapFindAt (fromLspPos uri pos) rmap
        let evals = trace ("Running eval for range " ++ showFullRange r) $ runEvalQueryFromRange allMods (r, rinfo) l
        let hc = J.InL $ J.mkMarkdown $ T.pack $ formatRangeInfoHover rinfo <> (if not (null evals) then "\n\nEvaluates to:\n\n" <> T.unpack (T.intercalate "\n\n" (map (T.pack . show) evals)) else "\n\nDemand CFA returned nothing")
            hover = J.Hover hc $ Just $ toLspRange r
        return hover
  case rsp of
    Nothing -> responder $ Right $ J.InR J.Null
    Just rsp -> responder $ Right $ J.InL rsp

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
