module Backend.Interp.Interp where


import Control.Monad
import Control.Monad.State (StateT (..), MonadState (..), liftIO)
import Control.Monad.Reader (ReaderT (..))
import qualified Data.Map.Strict as M
import Core.Core
import Compile.Module (Module (..))
import Common.Name (Name (..), qualifier, newQualified, newLocallyQualified, nameNil)
import Data.List (find)
import Data.Maybe
import Data.Text.Array (run)
import Core.Pretty (prettyExpr)
import Type.Pretty (defaultEnv)
import Lib.Trace (trace, traceM)
import Common.NamePrim
import qualified Data.Text as T

data Value =
  VInt Integer
  | VDouble Double
  | VChar Char
  | VString String
  | VCon Name [Value]
  | VClos Expr Env
  | VBox Addr
  | VPrim Name
  | VCCtxEmpty
  | VHole
  deriving (Show)
  -- | VCCtx Name [Value] [Value] -- Con, before values and after values

showValue :: Value -> String
showValue (VString s) = s

type Addr = Int

type Env = M.Map Name Value

data Handlers =
  HTop
  | HInt [Operations]

type Operations = [Expr]

type Interp a =  ReaderT Handlers (StateT (M.Map Addr Value, [Module]) IO) a

getDef :: Name -> Interp (Maybe Def)
getDef name = do
  (_, modules) <- get
  let nm = qualifier name
  let mmod = find (\m -> modName m == nm) modules
  case mmod of
    Nothing -> return Nothing
    Just mod ->
      return $ find (\def -> defName def == name) (flattenDefGroups $ coreProgDefs (fromJust (modCore mod)))

doInterpMain :: Name -> Interp ()
doInterpMain main = do
  def <- fromJust <$> getDef main
  traceM $ show (prettyExpr defaultEnv (defExpr def))
  doInterp (lamBodyMain $ defExpr def) M.empty
  return ()

lamBodyMain :: Expr -> Expr
lamBodyMain (Lam [] _ e) = lamBodyMain e
lamBodyMain (TypeLam _ e) = lamBodyMain e
lamBodyMain (TypeApp e _) = lamBodyMain e
lamBodyMain e = e

lookupVar :: Name -> Env -> Interp Value
lookupVar name env = do
  case M.lookup name env of
    Just val -> return val
    Nothing -> do
      let modules = qualifier name
      def <- getDef name
      case def of
        Just def -> doInterp (defExpr def) env
        Nothing -> return $ VPrim name

coreIntName s   = newQualified "std/core/int" s
nameIntMul = coreIntName "*"
nameIntDiv = coreIntName "/"
nameIntMod = coreIntName "%"
nameIntEq  = coreIntName "=="
nameIntLt  = coreIntName "<"
nameIntLe  = coreIntName "<="
nameIntGt  = coreIntName ">"
nameIntGe  = coreIntName ">="
nameIntOdd = coreIntName "is-odd"

coreCharName s   = newQualified "std/core/char" s
nameCoreCharLt = coreCharName "<"
nameCoreCharLtEq = coreCharName "<="
nameCoreCharGt = coreCharName ">"
nameCoreCharGtEq = coreCharName ">="
nameCoreCharEq = coreCharName "=="
nameIntChar = newLocallyQualified "std/core/char" "int" "char"
nameCoreCharToString = newLocallyQualified "std/core/string" "char" "@extern-string"
nameCoreStringListChar = newQualified "std/core/string" "list"
nameCoreStringPatCount = newLocallyQualified "std/core/string" "stringpat" "count"
nameCoreStringExternListChar = newQualified "std/core/string" "@extern-list"
nameCoreListCharString = newLocallyQualified "std/core/string" "listchar" "@extern-string"
nameCoreSliceString = newQualified "std/core/sslice" "@extern-string"

nameCoreTypesExternAppend = newQualified "std/core/types" "@extern-x++"
nameCoreIntExternShow = coreIntName "@extern-show"
nameCoreCharInt = coreCharName "int"
nameNumInt32Int = newQualified "std/num/int32" "int"
nameNumFloat64Int = newQualified "std/num/float64" "int"
nameNumFloat64Ceil = newQualified "std/num/float64" "ceiling"
nameNumFloat64Ln = newQualified "std/num/float64" "ln"
nameNumFloat64Div = newQualified "std/num/float64" "/"
nameNumFloat64IntFloat64 = newQualified "std/num/float64" "float64"
nameThrow = newQualified "std/core/exn" "throw"
namePretendDecreasing = newQualified "std/core/undiv" "pretend-decreasing"
nameUnsafeTotalCast = newQualified "std/core/unsafe" "unsafe-total-cast"
nameNumRandom = newQualified "std/num/random" "random-int"
nameCoreTrace = newQualified "std/core/debug" "trace"
nameCorePrint = newLocallyQualified "std/core/console" "string" "print"
nameCorePrintln = newLocallyQualified "std/core/console" "string" "println"
nameCoreXPrintsLn = newQualified "std/core/console" "@extern-xprintsln"
nameCoreSPrintln = newQualified "std/core/console" "printsln"
nameUnsafeNoState = newQualified "std/core/console" "unsafe-nostate"
nameEffectExternOpen = newQualified "std/core/types" "@extern-open"

primitives = [nameIntMul, nameIntDiv, nameIntMod, nameIntEq, nameIntLt, nameIntLe, nameIntGt, nameIntGe, nameIntOdd,
              nameCoreCharLt, nameCoreCharLtEq, nameCoreCharGt, nameCoreCharGtEq, nameCoreCharEq, nameCoreCharToString,
              nameCoreStringListChar, nameCoreSliceString, nameCoreTypesExternAppend, nameCoreIntExternShow,
              nameCoreCharInt, nameNumInt32Int, nameNumFloat64Int, nameNumFloat64Ceil, nameNumFloat64Ln, nameNumFloat64Div,
              nameNumFloat64IntFloat64, nameThrow, namePretendDecreasing, nameUnsafeTotalCast, nameNumRandom,
              nameCoreTrace, nameCorePrint, nameCorePrintln, nameCoreSPrintln, nameRef]

fromBool :: Bool -> Value
fromBool True = VCon nameTrue []
fromBool False = VCon nameFalse []

doInterp :: Expr -> Env -> Interp Value
doInterp e env = do
  traceM $ show (prettyExpr defaultEnv e)
  case e of
    Var name info -> lookupVar (getName name) env
    Lit lit -> case lit of
      LitInt i -> return $ VInt i
      LitFloat d -> return $ VDouble d
      LitChar c -> return $ VChar c
      LitString s -> return $ VString s
    App f args -> do
      fVal <- doInterp f env
      argsVals <- mapM (\arg -> doInterp arg env) args
      case fVal of
        VClos (Lam bindings _ body) env -> do
          let newBindings = zipWith (,) (map getName bindings) argsVals
          let newEnv = M.union (M.fromList newBindings) env
          doInterp body newEnv
        VCon name [] -> return $ VCon name argsVals
        VPrim name -> interpPrim name argsVals
        _ -> error $ "Not a function: " ++ showValue fVal
    Con name _ -> return $ VCon (getName name) []
    Lam{} -> return $ VClos e env
    Case scruts brnchs -> do
      scrutVals <- mapM (\scrut -> doInterp scrut env) scruts
      evalBranch scrutVals brnchs
      where
        evalBranch scrutVals brnchs =
          case findMatchingBranch scrutVals brnchs of
            Just (Branch pats [Guard guard body]:branches, binds) -> do
              let newEnv = M.union (M.fromList binds) env
              guard <- doInterp guard newEnv
              case guard of
                VCon nameTrue [] -> doInterp body newEnv
                _ -> evalBranch scrutVals branches -- if guard is false try next branch
            Nothing -> error $ "No matching branch: " ++ show scrutVals
    Let bs e ->
      do
        newEnv <- foldM (\acc def -> do
          let name = defName def
          val <- doInterp (defExpr def) acc
          return $ M.insert name val acc) env (flattenDefGroups bs)
        doInterp e newEnv
    TypeApp e _ -> doInterp e env
    TypeLam _ e -> doInterp e env

interpPrim name vals
  | name `elem` [nameCoreSPrintln, nameCoreXPrintsLn] = do
    let [argVal] = vals
    liftIO $ putStrLn $ showValue argVal
    return argVal
  | name == nameCoreIntExternShow = do
    let [VInt argVal] = vals
    return $ VString $ show argVal
  | name == nameCoreTypesExternAppend = do
    let [VString arg1, VString arg2] = vals
    return $ VString (arg1 ++ arg2)
  | name == nameCoreStringPatCount = do
    let [VString arg1, VString pat] = vals
    return $ VInt $ toInteger $ T.count (T.pack pat) (T.pack arg1)
  | name == nameCoreStringExternListChar = do
    let [VString a1] = vals
    return $ foldr (\c acc -> VCon nameCons [VChar c, acc]) (VCon nameListNil []) a1
  | name == nameCoreListCharString = do
    return $ VString $ foldr (\(VCon nameCons [VChar c, acc]) str -> c:str) "" vals
  | name == nameCoreCharLt = do
    let [VChar a1, VChar a2] = vals
    return $ fromBool $ a1 < a2
  | name == nameCoreCharGt = do
    let [VChar a1, VChar a2] = vals
    return $ fromBool $ a1 > a2
  | name == nameCoreCharToString = do
    let [VChar a1] = vals
    return $ VString [a1]
  | name == nameCoreCharInt = do
    let [VChar a1] = vals
    return $ VInt $ toInteger $ fromEnum a1
  | name == nameIntSub = do
    let [VInt a1, VInt a2] = vals
    return $ VInt $ a1 - a2
  | name == nameIntAdd = do
    let [VInt a1, VInt a2] = vals
    return $ VInt $ a1 + a2
  | name == nameIntMod = do
    let [VInt a1, VInt a2] = vals
    return $ VInt $ a1 `mod` a2
  | name == nameIntLe = do
    let [VInt a1, VInt a2] = vals
    return $ fromBool $ a1 <= a2
  | name == nameIntChar = do
    let [VInt a1] = vals
    return $ VChar $ toEnum $ fromInteger a1
  | name == nameNumFloat64IntFloat64 = do
    let [VInt a1] = vals
    return $ VDouble $ fromIntegral a1
  | name `elem` [nameEffectOpen, nameEffectExternOpen, nameUnsafeNoState, nameUnsafeTotalCast, namePretendDecreasing] = do
    let [f] = vals
    return f
  | name == nameRef = do
    let [val] = vals
    a <- freshAddr
    store a val
    return $ VBox a
  | name == nameDeref = do
    let [VBox a] = vals
    (store, _) <- get
    return $ store M.! a
  | otherwise = error $ "Unknown primitive: " ++ show name

freshAddr :: Interp Addr
freshAddr = do
  (store, _) <- get
  return $ M.size store

store :: Addr -> Value -> Interp ()
store a val = do
  (store, modules) <- get
  put (M.insert a val store, modules)

findMatchingBranch :: [Value] -> [Branch] -> Maybe ([Branch], [(Name, Value)])
findMatchingBranch _ [] = Nothing
findMatchingBranch scrutVals allb@(Branch pats _:branches) =
  let matches = zipWith findMatchingPattern scrutVals pats in
  if all isJust matches then
    Just (allb, fromJust $ head matches)
  else
    findMatchingBranch scrutVals branches
  where
    findMatchingPattern :: Value -> Pattern -> Maybe [(Name, Value)]
    findMatchingPattern v (PatVar n pat) =
      case findMatchingPattern v pat of
        Just binds -> Just $ (getName n, v):binds
        Nothing -> Nothing
    findMatchingPattern (VCon n1 vals) (PatCon {patConName=n2,patConPatterns= pats}) =
      if n1 == getName n2 then
        let matches = zipWith findMatchingPattern vals pats in
        if all isJust matches then
          Just $ concatMap fromJust matches
        else
          Nothing
      else
        Nothing
    findMatchingPattern (VInt i) (PatLit (LitInt j)) = if i == j then Just [] else Nothing
    findMatchingPattern (VDouble i) (PatLit (LitFloat j)) = if i == j then Just [] else Nothing
    findMatchingPattern (VChar i) (PatLit (LitChar j)) = if i == j then Just [] else Nothing
    findMatchingPattern (VString i) (PatLit (LitString j)) = if i == j then Just [] else Nothing
    findMatchingPattern v PatWild = Just []
    findMatchingPattern _ _ = Nothing




interp :: Name -> [Module] -> IO ()
interp mainEntry modules = do
  runStateT (runReaderT (doInterpMain mainEntry) HTop) (M.empty, modules)
  return ()
