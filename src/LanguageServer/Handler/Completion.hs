-----------------------------------------------------------------------------
-- The LSP handler that provides code completions
-----------------------------------------------------------------------------
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

module LanguageServer.Handler.Completion
  ( completionHandler,
  )
where

import Common.Name (Name (..))
import Compiler.Module (Loaded (..))
import Compiler.Options (Flags)
import Control.Lens ((^.))
import qualified Data.Map as M
import Data.Maybe (maybeToList, fromMaybe, fromJust)
import qualified Data.Text as T
import qualified Data.Text.Utf16.Rope as Rope
import qualified Data.Set as S
import qualified Data.Text as T
import Kind.Constructors (ConInfo (..), Constructors, constructorsList)
import Kind.Synonym (SynInfo (..), Synonyms, synonymsToList)
import Language.LSP.Server (Handlers, getVirtualFile)
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Lens as J
import Language.LSP.VFS (VirtualFile (VirtualFile))
import LanguageServer.Monad (LSM, getLoaded, requestHandler)
import Lib.PPrint (Pretty (..))
import Syntax.Lexer (reservedNames)
import Type.Assumption
  ( Gamma,
    NameInfo
      ( InfoCon,
        InfoExternal,
        InfoFun,
        InfoImport,
        InfoVal,
        infoAlias,
        infoArity,
        infoCName,
        infoCon,
        infoFormat,
        infoFullName,
        infoIsVar,
        infoRange,
        infoType,
        infoVis
      ),
    gammaList,
  )
import qualified Language.LSP.Protocol.Message as J
import Data.Char (isUpper, isAlphaNum)
import Compiler.Compile (Module (..))
import Type.Type (Type(..), splitFunType)
import Syntax.RangeMap (rangeMapFindAt, rangeInfoType)
import LanguageServer.Conversions (fromLspPos)
import Common.Range (makePos, posNull, Range, rangeNull)
import LanguageServer.Handler.Hover (formatRangeInfoHover)
import Type.Unify (runUnify, unify, runUnifyEx, matchArguments)
import Data.Either (isRight)
import Lib.Trace (trace)
import Type.InferMonad (subst)
import Type.TypeVar (tvsEmpty)

completionHandler :: Flags -> Handlers LSM
completionHandler flags = requestHandler J.SMethod_TextDocumentCompletion $ \req responder -> do
  let J.CompletionParams doc pos _ _ context = req ^. J.params
      uri = doc ^. J.uri
      normUri = J.toNormalizedUri uri
  loaded <- getLoaded
  vfile <- getVirtualFile normUri
  let items = do
        l <- maybeToList loaded
        vf <- maybeToList vfile
        pi <- maybeToList =<< getCompletionInfo pos vf (loadedModule l) uri
        findCompletions l pi
  responder $ Right $ J.InL items

-- | Describes the line at the current cursor position
data PositionInfo = PositionInfo
  { fullLine :: !T.Text
    -- ^ The full contents of the line the cursor is at
  , argument :: !T.Text
  , searchTerm :: !T.Text
  , cursorPos :: !J.Position
    -- ^ The cursor position
  , argumentType :: Maybe Type
  , isFunctionCompletion :: Bool
  } deriving (Show,Eq)

getCompletionInfo :: Monad m => J.Position -> VirtualFile -> Module -> J.Uri -> m (Maybe PositionInfo)
getCompletionInfo pos@(J.Position l c) (VirtualFile _ _ ropetext) mod uri =
      let rm = (fromJust $ modRangeMap mod) in
      let result = Just $ fromMaybe (PositionInfo "" "" "" pos Nothing False) $ do -- Maybe monad
            let lastMaybe [] = Nothing
                lastMaybe xs = Just $ last xs

            let currentRope = fst $ Rope.splitAtLine 1 $ snd $ Rope.splitAtLine (fromIntegral l) ropetext
            beforePos <- Rope.toText . fst <$> Rope.splitAt (fromIntegral c + 1) currentRope
            currentWord <-
                if | T.null beforePos -> Just ""
                   | T.last beforePos == ' ' -> Just "" -- Up to whitespace but not including it
                   | otherwise -> lastMaybe (T.words beforePos)

            let parts = T.split (=='.') -- The () are for operators and / is for qualified names otherwise everything must be adjacent
                          $ T.takeWhileEnd (\x -> isAlphaNum x || x `elem` ("()-_./'"::String)) currentWord

            case reverse parts of
              [] -> Nothing
              (x:xs) -> do
                trace ("parts: " ++ show parts) $ return ()
                let modName = case filter (not .T.null) xs of {x:xs -> x; [] -> ""}
                argumentText <- Rope.toText . fst <$> Rope.splitAt (fromIntegral c) currentRope
                let isFunctionCompletion = if | T.null argumentText -> False
                                              | T.findIndex (== '.') argumentText > T.findIndex (== ' ') argumentText -> True
                                              | otherwise -> False
                    newC = c - fromIntegral (T.length x + (if isFunctionCompletion then 1 else 0))
                let currentType =
                      if isFunctionCompletion then
                          let currentRange = fromLspPos uri (J.Position l newC) in
                          do
                            (range, rangeInfo) <- rangeMapFindAt currentRange rm
                            t <- rangeInfoType rangeInfo
                            case splitFunType t of
                              Just (pars,eff,res) -> Just res
                              Nothing             -> Just t
                      else Nothing
                -- currentRope is already a single line, but it may include an enclosing '\n'
                let curLine = T.dropWhileEnd (== '\n') $ Rope.toText currentRope
                let pi = PositionInfo curLine modName x pos currentType isFunctionCompletion
                return $ trace (show pi) pi
            in
      trace (show result) $ return result

-- TODO: Make completions context-aware
-- TODO: Complete local variables
-- TODO: Show documentation comments in completion docs

filterPrefix :: PositionInfo -> T.Text -> Bool
filterPrefix pinfo n = (searchTerm pinfo `T.isPrefixOf` n) && ('.' /= T.head n)

findCompletions :: Loaded -> PositionInfo -> [J.CompletionItem]
findCompletions loaded pinfo@PositionInfo{isFunctionCompletion = fcomplete} = filter (filterPrefix pinfo . (^. J.label)) completions
  where
    curModName = modName $ loadedModule loaded
    search = searchTerm pinfo
    gamma = loadedGamma loaded
    constrs = loadedConstructors loaded
    syns = loadedSynonyms loaded
    completions =
      if fcomplete then valueCompletions curModName gamma pinfo else keywordCompletions curModName
        ++ valueCompletions curModName gamma pinfo
        ++ constructorCompletions curModName constrs
        ++ synonymCompletions curModName syns

-- TODO: Type completions, ideally only inside type expressions
-- ++ newtypeCompletions ntypes

typeUnifies :: Type -> Maybe Type -> Bool
typeUnifies t1 t2 =
  case t2 of
    Nothing -> True
    Just t2 ->  let (res, _, _) = (runUnifyEx 0 $ matchArguments True rangeNull tvsEmpty t1 [t2] []) in  isRight res

valueCompletions :: Name -> Gamma -> PositionInfo -> [J.CompletionItem]
valueCompletions curModName gamma pinfo@PositionInfo{argumentType=tp, searchTerm=search} = map toItem . filter matchInfo $ filter (\(n, ni) -> filterPrefix pinfo $ T.pack $ nameId n) $ gammaList gamma
  where
    matchInfo :: (Name, NameInfo) -> Bool
    matchInfo (n, ninfo) = case ninfo of
        InfoVal {..} -> True
        InfoFun {infoType} -> trace ("Checking " ++ show n) typeUnifies infoType tp
        InfoExternal {infoType} -> trace ("Checking " ++ show n) typeUnifies infoType tp
        InfoImport {infoType} -> trace ("Checking " ++ show n) typeUnifies infoType tp
        InfoCon {infoType } -> trace ("Checking " ++ show n) typeUnifies infoType tp
    toItem (n, ninfo) = makeCompletionItem curModName n k d
      where
        k = case ninfo of
          InfoVal {..} -> J.CompletionItemKind_Constant
          InfoFun {..} -> J.CompletionItemKind_Function
          InfoExternal {..} -> J.CompletionItemKind_Reference
          InfoImport {..} -> J.CompletionItemKind_Module
          InfoCon {infoCon = ConInfo {conInfoParams = ps}}
            | not (null ps) -> J.CompletionItemKind_Constructor
            | otherwise -> J.CompletionItemKind_EnumMember
        d = show $ pretty $ infoType ninfo

constructorCompletions :: Name -> Constructors -> [J.CompletionItem]
constructorCompletions curModName = map toItem . constructorsList
  where
    toItem (n, cinfo) = makeCompletionItem curModName n k d
      where
        ps = conInfoParams cinfo
        k
          | not (null ps) = J.CompletionItemKind_Constructor
          | otherwise = J.CompletionItemKind_EnumMember
        d = show $ pretty $ conInfoType cinfo

synonymCompletions :: Name -> Synonyms -> [J.CompletionItem]
synonymCompletions curModName = map toItem . synonymsToList
  where
    toItem sinfo = makeCompletionItem curModName n J.CompletionItemKind_Interface d
      where
        n = synInfoName sinfo
        d = show $ pretty $ synInfoType sinfo

keywordCompletions :: Name -> [J.CompletionItem]
keywordCompletions curModName  = map toItem $ S.toList reservedNames
  where
    toItem s = makeSimpleCompletionItem curModName s J.CompletionItemKind_Keyword

makeCompletionItem :: Name -> Name -> J.CompletionItemKind -> String -> J.CompletionItem
makeCompletionItem curModName n k d =
  J.CompletionItem
    label
    labelDetails
    kind
    tags
    detail
    doc
    deprecated
    preselect
    sortText
    filterText
    insertText
    insertTextFormat
    insertTextMode
    textEdit
    textEditText
    additionalTextEdits
    commitChars
    command
    xdata
  where
    label = T.pack $ nameId n
    labelDetails = Nothing
    kind = Just k
    tags = Nothing
    detail = Just $  T.pack d
    doc = Just $ J.InL $ T.pack $ nameModule n
    deprecated = Just False
    preselect = Nothing
    sortText = Just $ if nameId curModName == nameModule n then T.pack $ "0" ++ nameId n else T.pack $ "2" ++ nameId n
    filterText = Nothing
    insertText = Nothing
    insertTextFormat = Nothing
    insertTextMode = Nothing
    textEdit = Nothing
    textEditText = Nothing
    additionalTextEdits = Nothing
    commitChars = Just [T.pack "\t"]
    command = Nothing
    xdata = Nothing

makeSimpleCompletionItem :: Name -> String -> J.CompletionItemKind -> J.CompletionItem
makeSimpleCompletionItem curModName l k =
  J.CompletionItem
    label
    labelDetails
    kind
    tags
    detail
    doc
    deprecated
    preselect
    sortText
    filterText
    insertText
    insertTextFormat
    insertTextMode
    textEdit
    textEditText
    additionalTextEdits
    commitChars
    command
    xdata
  where
    label = T.pack l
    labelDetails = Nothing
    kind = Just k
    tags = Nothing
    detail = Nothing
    doc = Nothing
    deprecated = Just False
    preselect = Nothing
    sortText = Just $ T.pack $ "1" ++ l
    filterText = Nothing
    insertText = Nothing
    insertTextFormat = Nothing
    insertTextMode = Nothing
    textEdit = Nothing
    textEditText = Nothing
    additionalTextEdits = Nothing
    commitChars = Just [T.pack "\t"]
    command = Nothing
    xdata = Nothing
