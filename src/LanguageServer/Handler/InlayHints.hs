-----------------------------------------------------------------------------
-- The LSP handler that provides hover tooltips
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

module LanguageServer.Handler.InlayHints (inlayHandler) where

import Compiler.Module (loadedModule, modRangeMap, Loaded (loadedModules), Module (modPath, modSourcePath))
import Control.Lens ((^.))
import Common.Range (Range (..), rangeEnd, Pos(..), rangeNull, posNull)
import qualified Data.Map as M
import qualified Data.Text as T
import Language.LSP.Server (Handlers, sendNotification, requestHandler)
import qualified Language.LSP.Protocol.Lens as J
import LanguageServer.Conversions (fromLspPos, toLspRange, toLspPos, fromLspRange)
import LanguageServer.Monad (LSM, getLoaded, getLoadedModule)
import Lib.PPrint (Pretty (..))
import Syntax.RangeMap (NameInfo (..), RangeInfo (..), rangeMapFindIn)
import qualified Language.LSP.Protocol.Message as J
import qualified Language.LSP.Protocol.Types as J
import LanguageServer.Handler.Hover (formatRangeInfoHover)
import Debug.Trace (trace)
import Data.Maybe (mapMaybe)

inlayHandler :: Handlers LSM
inlayHandler = requestHandler J.SMethod_TextDocumentInlayHint $ \req responder -> do
  let J.InlayHintParams prog doc rng = req ^. J.params
      uri = doc ^. J.uri
      newRng = fromLspRange uri rng
  loaded <- getLoadedModule uri
  let toInlayHint :: (Range, RangeInfo) -> Maybe J.InlayHint
      toInlayHint (rng, rngInfo) =
        let rngEnd = rangeEnd rng
            shouldShow =
              (rngEnd /= posNull) &&
              case rngInfo of
              Id _ info _ -> case info of
                NIValue _ inf -> inf
                NICon _ inf -> False
                NITypeCon _ inf -> False
                NITypeVar _ inf -> False
                NIModule -> False
                NIKind -> False
              Decl{} -> False
              Block _ -> False
              Error _ -> False
              Warning _ -> False
        in
        if shouldShow then
          Just $ J.InlayHint (toLspPos rngEnd{posColumn = posColumn rngEnd + 1}) (J.InL $ T.pack $ formatInfo rngInfo) (Just J.InlayHintKind_Type) Nothing Nothing (Just True) (Just True) Nothing
        else Nothing
      rsp = do
        l <- loaded
        rmap <- modRangeMap l
        return $ mapMaybe toInlayHint $ rangeMapFindIn newRng rmap
  case rsp of
    Nothing -> responder $ Right $ J.InR J.Null
    Just rsp -> responder $ Right $ J.InL rsp


-- Pretty-prints type/kind information to a hover tooltip
formatInfo :: RangeInfo -> String
formatInfo rinfo = case rinfo of
  Id qname info isdef ->
    case info of
      NIValue tp _ -> " : " ++ show (pretty tp)
      NICon tp _ -> ""
      NITypeCon k _ -> ""
      NITypeVar k _ -> ""
      NIModule -> ""
      NIKind -> ""
  Decl s name mname -> ""
  Block s -> ""
  Error doc -> "Error: " ++ show doc
  Warning doc -> "Warning: " ++ show doc