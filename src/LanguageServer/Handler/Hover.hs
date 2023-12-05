-----------------------------------------------------------------------------
-- The LSP handler that provides hover tooltips
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

module LanguageServer.Handler.Hover (hoverHandler, formatRangeInfoHover) where

import Compiler.Module (loadedModule, modRangeMap, Loaded (loadedModules, loadedImportMap), Module (modPath, modSourcePath))
import Control.Lens ((^.))
import qualified Data.Map as M
import qualified Data.Text as T
import Language.LSP.Server (Handlers, sendNotification, requestHandler)
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Lens as J
import LanguageServer.Conversions (fromLspPos, toLspRange)
import LanguageServer.Monad
    ( LSM,
      getLoaded,
      getLoadedModule,
      getHtmlPrinter,
      getFlags,
      LSM,
      getLoaded,
      getLoadedModule,
      putLoaded )
import Lib.PPrint
    ( Pretty(..), Doc, text, (<+>), color, Pretty(..) )
import Syntax.RangeMap
    ( NameInfo(..),
      RangeInfo(..),
      rangeMapFindAt,
      NameInfo(..),
      RangeInfo(..),
      rangeMapFindAt )
import qualified Language.LSP.Protocol.Message as J
import Control.Monad.Cont (liftIO)
import Type.Pretty (ppScheme, defaultEnv, Env(..), ppName, ppType)
import Common.ColorScheme (ColorScheme (colorNameQual, colorSource), Color (Gray))
import Kind.Pretty (prettyKind)
import Common.Name (nameNil)
import Kind.ImportMap (importsEmpty, ImportMap)
import Compiler.Options (Flags, colorSchemeFromFlags, prettyEnvFromFlags)
import Compiler.Compile (modName)
import Type.Type (Name)
import Core.DemandAnalysis (runEvalQueryFromRangeSource, AnalysisKind (..))
import Debug.Trace (trace)
import Common.Range (showFullRange)
import LanguageServer.Handler.TextDocument (getCompile)
import Core.StaticContext (showSyntax, showLit, showSyntaxDef)
import qualified Data.Set as S
import Data.List (intercalate)
import Data.Time (diffUTCTime)
import Data.Time.Clock (getCurrentTime)

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
  in T.pack hc

hoverHandler :: Handlers LSM
hoverHandler = requestHandler J.SMethod_TextDocumentHover $ \req responder -> do
  let J.HoverParams doc pos _ = req ^. J.params
      uri = doc ^. J.uri
  loadedMod <- getLoadedModule uri
  loaded <- getLoaded uri
  compile <- getCompile
  flags <- getFlags
  let res = do
        mod <- loadedMod
        l <- loaded
        rmap <- modRangeMap mod
        (r, rinfo) <- rangeMapFindAt (fromLspPos uri pos) rmap
        return (modName mod, l, r, rinfo)
  case res of
    Just (mName, l, r, rinfo) -> do
      print <- getHtmlPrinter
      let imports = loadedImportMap l
      let mod = loadedModule l
      tstart <- liftIO getCurrentTime
      (!xs, !newLoaded) <- return $ trace ("Running eval for position " ++ show (fromLspPos uri pos)) $ runEvalQueryFromRangeSource l compile (r, rinfo) mod HybridEnvs 2
      tend <- liftIO getCurrentTime
      putLoaded newLoaded
      x <- liftIO $ formatRangeInfoHover print flags mName imports rinfo
      let hc = J.InL $ J.mkMarkdown $ x <> T.intercalate "\n\n" (map toAbValueText xs) <> "\n\n" <> T.pack (show $ diffUTCTime tend tstart)
          rsp = J.Hover hc $ Just $ toLspRange r
      responder $ Right $ J.InL rsp
    Nothing -> responder $ Right $ J.InR J.Null

prettyEnv flags ctx imports = (prettyEnvFromFlags flags){ context = ctx, importsMap = imports }

-- Pretty-prints type/kind information to a hover tooltip
formatRangeInfoHover :: (Doc -> IO T.Text) -> Flags -> Name -> ImportMap -> RangeInfo -> IO T.Text
formatRangeInfoHover print flags mName imports rinfo =
  let colors = colorSchemeFromFlags flags
      env = prettyEnv flags mName imports in
  case rinfo of
  Id qname info isdef ->
    print $ (ppName env{colors=colors{colorSource = Gray}} qname) <+> text " : " <+> case info of
      NIValue tp -> ppScheme env tp
      NICon tp ->  ppScheme env tp
      NITypeCon k -> prettyKind colors k
      NITypeVar k -> prettyKind colors k
      NIModule -> text "module"
      NIKind -> text "kind"
  Decl s name mname -> print $ text s <+> text " " <+> pretty name
  Block s -> return $ T.pack s
  Error doc -> print $ text "Error: " <+> doc
  Warning doc -> print $ text "Warning: " <+> doc
