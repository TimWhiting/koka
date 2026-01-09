{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use map with tuple-section" #-}
module Core.FlowAnalysis.Full.DMCFA.DMCFA where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Full.DMCFA.AbstractValue
import Core.FlowAnalysis.Full.DMCFA.Monad
import Core.FlowAnalysis.Full.DMCFA.Primitives
import Core.FlowAnalysis.Full.PrimComm
import Core.Core
import Data.Int (Int)
import Common.Name
import Debug.Trace (trace)
import Common.NamePrim
import Data.Maybe (fromJust, isJust)
import Compile.Module (Module(..))
import Common.Failure (HasCallStack)
import Type.Type (splitFunType, typeAny, splitFunScheme, Effect, typeTotal, effectExtend, extractEffectExtend, labelName)
import Control.Monad (foldM, zipWithM, zipWithM_)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)
import Type.Pretty (defaultEnv, ppType)
import Lib.PPrint (hcat, tupled, vcat, text)
import Common.File (startsWith, endsWith)
import Syntax.Syntax (ValueBinder(binderName))
import Data.List (intercalate)

doStep :: HasCallStack => FixInput -> FixAAMR r s e FixChange
doStep i =
  memo i $ do
    case i of
      VStore UnitAddr -> return $ SV changeUnit
      VStore addr ->
        trace ("Value not found in store :" ++ show addr)
        doBottom
      KStore addr -> if addr == EndKAddr then return $ KV EndKAddr else doBottom
      Step (CEval expr venv ctx) -> doEval expr venv ctx
      Step (CApply kaddr addr ctx) -> doApply kaddr addr ctx
      Step (CContinue res frame ctx) -> doContinue res frame ctx
      Step (CHandleEffects res venv bodId hnd retCtx) -> doHandleEffects res venv bodId hnd retCtx
      Step (CHandleLocal res venv bodId varName valAddr retCtx) -> doHandleLocal res venv bodId varName valAddr retCtx

extendStore :: Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  -- case addr of
  --   BindImplicitAddr{} -> return ()
  --   ConImplicitAddr{} -> return ()
  --   _ -> trace ("Extending store: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (VStore addr) (SV v)
extendKStore :: Addr -> Addr -> FixAAMR r e s ()
extendKStore addr v = do
  -- trace ("Extending KStore: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (KStore addr) (KV v)

store addr = do
  SV res <- doStep (VStore addr)
  return res
kStore addr = do
  KV res <- doStep (KStore addr)
  return res

unreturnV :: FixAAMR r s e FixChange -> FixAAMR r s e RValue
unreturnV f = do
  RV r <- f
  return r
returnV :: FixAAMR r s e RValue -> FixAAMR r s e FixChange
returnV f = RV <$> f
eval expr venv ctx = unreturnV $ doStep $ Step (CEval expr venv ctx)
apply kaddr addr ctx = unreturnV $ doStep $ Step (CApply kaddr addr ctx)
continue res frame ctx = unreturnV $ doStep $ Step (CContinue res frame ctx)
handleEffects res venv bodId hnd retCtx = unreturnV $ doStep $ Step (CHandleEffects res venv bodId hnd retCtx)
handleLocal res venv bodId varName valAddr retCtx = unreturnV $ doStep $ Step (CHandleLocal res venv bodId varName valAddr retCtx)

returnConst :: VEnv -> CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e FixChange
returnConst env ctx expr v = RV . RVAddr <$> allocConst env ctx expr v
returnOp :: DelimitedVal -> StaticCtx -> Frame ->  DelimitedFrame -> Addr -> FixAAMR r s e FixChange
returnOp dval ctx frame dframe kaddr = return $ RV $ ROp dval ctx frame dframe kaddr
returnAddr :: Addr -> FixAAMR r s e FixChange
returnAddr addr = return $ RV $ RVAddr addr


allocConst :: VEnv -> CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst env ctx expr v = do
  let addr = BindImplicitAddr ctx (limitEnv env (fvs expr)) (contextId expr)
  extendStore addr v
  return addr

fvsl :: [ExprContext] -> S.Set TName
fvsl exprs = S.unions $ map fvs exprs

doEval :: HasCallStack => ExprContext -> VEnv -> CombinedCtx -> FixAAMR r s e FixChange
doEval expr venv ctx = do
  let open = case exprOfCtx expr of
        App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen -> True
        _ -> False
      isSimpleExpr e = case e of
        Var{} -> True
        Lit{} -> True
        Con{} -> True
        Lam{} -> True
        TypeApp e _ -> isSimpleExpr e
        TypeLam _ e -> isSimpleExpr e
        App (Var nm _) _ _ |  getName nm `elem` [nameHTag, nameEvvAt, nameSSizeT] -> True
        App (TypeApp (Var nm _) _) _ _ | isConstructorName (getName nm) || getName nm `elem` [nameHTag, nameEvvAt, nameSSizeT] -> True
        App (App (TypeApp (Var nm _) _) [e] _) _ _ -> getName nm == nameEffectOpen
        -- App e _ _ -> isSimpleExpr e
        _ -> False -- Essentially just Let / Case
      process x = if not open && not (isSimpleExpr (exprOfCtx expr)) then do
                    -- analysisLog ("Evaluating: " ++ showCtxExpr expr ++ ":" ++ show ctx ++ " with env " ++ show venv)
                    x
                  else x-- trace ("Evaluating: " ++ show expr ++ " in " ++ show (M.toList venv) ++ " : " ++ show ctx) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
   in process $ case exprOfCtx expr of
    App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen || getName name == namePretendDecreasing -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      returnV $ eval f venv ctx
    App (TypeApp (Var name _) _) [_,_,f] _ | getName name == nameMaskAt -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 3 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f venv ctx
      returnV $ continue res FMask ctx
    App (TypeApp (Var name _) _) [f] _ | getName name == nameMaskBuiltin -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f venv ctx
      returnV $ continue res FMask ctx
    Con tn _ _ -> do
      let params = case splitFunScheme (typeOf tn) of
                      Just (_, params, _, _) -> map fst params
                      Nothing -> []
      -- trace ("Con: " ++ show tn ++ " with params: " ++ show params) $ return ()
      let constr = AChangeConstr expr params
      returnConst venv ctx expr constr
    Var name _ -> do
      if isPrimitive name && not (isTrickyPrimitive name) then do
        -- trace ("Primitive " ++ show name) $ return ()
        returnConst venv ctx expr (AChangePrim name expr)
      else if qualifier (getName name) == nameCoreHnd then
        error ("Unexpected handler library name in DMCFA: " ++ show name)
      else case lookupEnv name venv of
        Just addr -> returnAddr addr
        Nothing -> do
          -- trace ("Evaluating external: " ++ show name) $ return ()
          res <- bindExternal (equalPrimitive name)
          case res of
            Just expr -> do
              c <- startCombinedCtx
              returnV $ eval expr M.empty c
            Nothing -> trace ("Variable not found: " ++ show name) doBottom
    Lit l -> returnConst venv ctx expr (injLit (contextId expr) l)
    Lam{} -> returnConst venv ctx expr (AChangeClos expr venv)
    App _ args _ -> doApp args
    Let dgs _ -> do
      child <- childrenContexts expr
      -- trace ("LetChildren: " ++ intercalate "\n" (map show child)) $ return ()
      bind <- focusLetDefBinding 0 0 expr
      let defGroup = head dgs
      let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
      let defName = defTName (defOfCtx bind)
      -- trace ("Let binding: " ++ show defName ++ " in " ++ show newEnv) $ return ()
      res <- eval bind (limitEnv newEnv (S.insert defName (fvs bind))) ctx
      returnV $ continue res (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr newEnv) ctx
    TypeApp{} -> do
      e <- focusChild 0 expr
      returnV $ eval e venv ctx
    TypeLam _ Lam{} -> returnConst venv ctx expr (AChangeClos expr venv)
    TypeLam _ (App _ args _) -> doApp args
    TypeLam _ _ -> do --(TypeApp Var{} _)
      childs <- childrenContexts expr
      -- trace ("TypeLam: " ++ show (map contextId childs)) $ return ()
      e <- focusChild 0 expr
      returnV $ eval e venv ctx
    Case _ brs -> do
      s <- focusScrutinee expr
      branches <- mapM (\i -> focusBranch i expr) [0..length brs - 1]
      res <- eval s (limitEnv venv (fvs s)) ctx
      returnV $ continue res (FScrut expr branches venv) ctx
    -- TypeLam _ e -> do
    --   trace ("TypeLam not handled yet: " ++ show e) $ doBottom
  where doApp args = do
          f <- focusFun expr
          argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
          -- trace ("Applying function: " ++ show f ++ " to args: " ++ show argExprs ++ " with env " ++ show venv) $ return ()
          res <- eval f (limitEnv venv (fvs f)) ctx
          returnV $ continue res (FApp (length args) argExprs [] expr venv) ctx

doContinue :: HasCallStack => RValue -> Frame -> CombinedCtx -> FixAAMR r s e FixChange
doContinue res frame ctx =
  case res of
    ROp dval ctx' frame' dframe knext -> do
      -- trace ("Capturing frame: " ++ show frame) $ do
      let k' = KAddr frame' ctx' dframe dval 
      extendKStore k' knext
      returnOp dval (static ctx) frame dframe k'
    RVAddr addr -> 
      -- trace ("Continuing: with frame " ++ show frame ++ " in " ++ show ctx) $ do
      case frame of
          FrameDone -> returnAddr addr
          f | f == FMask -> do
            v <- store addr
            case v of
              AChangeClos e env -> do
                bod <- focusBody e
                returnV $ eval bod env ctx
          FApp n args res eApp venv -> do
            let uApp = contextId eApp
            case args of
              [] -> case res ++ [addr] of
                f:arguments -> do
                  res <- store f
                  case res of
                    AChangeClos cexpr cenv -> do
                      body <- focusBody cexpr
                      let args = lamNames cexpr
                      m <- mLimit
                      let newCtx = addCall m ctx uApp
                      let newEnv = foldl (\acc x -> M.insert x newCtx acc) cenv args
                      -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show args) $ return ()
                      zipWithM_ (\a p -> do
                        val <- store p
                        extendStore (fromJust $ lookupEnv a newEnv) val) args arguments
                      returnV $ eval body (limitEnv newEnv (fvs body)) newCtx
                    AChangePrim name pms -> do
                      let retAddr = BindImplicitAddr ctx venv uApp
                      let n = getName name
                      if not (isHandlerPrimitive n) then do
                        args <- mapM store arguments
                        res <- doPrimitive n args
                        extendStore retAddr res
                        returnAddr retAddr
                      else doHandlerPrimitive name n retAddr arguments venv ctx eApp
                    AChangeConstr con params -> do
                      let name = case exprOfCtx con of
                            Con n _ _ -> n
                            _ -> error "Expected a constructor"
                      let retAddr = BindImplicitAddr ctx venv uApp
                      let conParams = map (\nm -> ConImplicitAddr nm ctx uApp) params
                      zipWithM_ rebind arguments conParams
                      extendStore retAddr (AChangeObj con name (zip params conParams))
                      -- extendStore addr (AChangeObj con name (zip params arguments))
                      returnAddr retAddr
                    AChangeKont kx henv hnd -> do
                      m <- mLimit
                      d <- dLimit
                      let newCtx = addCall m ctx uApp
                          newDynCtx = addDelim d newCtx uApp (hLabel hnd)
                      -- trace ("Applying continuation\n" ++ show uApp ++ "\n" ++ show newCtx ++ "\n" ++ show newDynCtx) $ return () -- ++ "for\n" ++
                      res <- apply kx addr newDynCtx
                      returnV $ handleEffects res henv uApp hnd newCtx
                    _ -> do
                      trace ("Applying non function: " ++ show res) doBottom
              next:rest -> do
                -- trace ("Next " ++ show next) $ return ()
                ret <- eval next (limitEnv venv (fvs next)) ctx
                returnV $ continue ret (FApp n rest (res ++ [addr]) eApp venv) ctx
          FLet groupIdx numGroups bindingIdx numBindings name resolved u venv -> do
            -- trace ("Applying Let " ++ show newctx ++ " env " ++ show venv) $ return ()
            val <- store addr
            let env' = M.insert name ctx venv -- We need to override the old name binding (in case it was in a different context)
            extendStore (fromJust $ lookupEnv name env') val
            -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show venv ) $ return ()
            -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
            if isLetDefBindingFinished groupIdx bindingIdx u then do
              -- trace ("Let group finished: " ++ show groupIdx ++ " of " ++ show numGroups) $ return ()
              body <- focusLetBod u
              returnV $ eval body (limitEnv env' (fvs body)) ctx
            else do
              -- trace ("Let group next: " ++ show groupIdx ++ ", " ++ show bindingIdx) $ return ()
              next <- focusNextLetDefBinding groupIdx bindingIdx u
              ret <- eval next env' ctx
              returnV $ continue ret (nextLetFrame frame ctx) ctx
          FScrut parent branches env -> do
            let recur [] = doBottom
                recur ((branch, expr):branches) = do
                  match <- branchMatch branch addr
                  case match of
                    Just (bindings, matchTree) -> do
                      let newEnv = foldl (\acc tname -> M.insert tname ctx acc) env (M.keys bindings)
                      mapM_ (\(tname, extend) ->
                        extend (fromJust $ lookupEnv tname newEnv)
                        ) (M.toList bindings)
                      each [
                        returnV $ eval expr (limitEnv newEnv (fvs expr)) ctx,
                        recur branches
                        ]
                    Nothing -> recur branches
            case exprOfCtx parent of
              Case _ pats -> recur (zip pats branches)
          FDollar va -> do
            res <- store va
            case res of
              AChangeClos cexpr cenv -> do
                  body <- focusBody cexpr
                  let [arg] = lamNames cexpr
                  let newEnv = M.insert arg ctx cenv
                  v <- store addr
                  extendStore (fromJust $ lookupEnv arg newEnv) v
                  returnV $ eval body (limitEnv newEnv (fvs body)) ctx
          FResume retCtx kont venv hnd u -> do
            m <- mLimit
            d <- dLimit
            let newRetCtx = addCall m ctx u
                newDelimCtx = addDelim d newRetCtx u (hLabel hnd)
            -- trace ("Applying continuation " ++ show (contextId u) ++ " " ++ show henv ) $ return () -- ++ "for\n" ++ 
            res <- apply kont addr newDelimCtx
            returnV $ handleEffects res venv u hnd newRetCtx
          _ -> do
            error ("Continuing: " ++ show res ++ " with unknown frame " ++ show frame)

doApply :: HasCallStack => Addr -> Addr -> DynamicCtx -> FixAAMR r s e FixChange
doApply kaddr addr delimCtx = do
  -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show dynctx) $ return ()
  -- trace ("Applying: " ++ show k) $ return ()
  case kaddr of
    EndKAddr -> returnAddr addr
    KAddr (FRestoreDelim (DFrameLocal venv bodId varName varAddr)) ctx _ _ -> do
      let newCtx = CombinedCtx ctx delimCtx
      d <- dLimit
      m <- mLimit
      let newRetCtx = addCall m newCtx bodId
      let newDelimCtx = newDelim d m newRetCtx bodId (getName varName)
      knext <- kStore kaddr
      res <- apply knext addr (dynamic newDelimCtx)
      returnV $ handleLocal res venv bodId varName varAddr newRetCtx
    KAddr (FRestoreDelim (DFrame venv bodId h)) ctx _ _ -> do
      let newCtx = CombinedCtx ctx delimCtx
      d <- dLimit
      m <- mLimit
      let newRetCtx = addCall m newCtx bodId
      let newDelimCtx = newDelim d m newRetCtx bodId (hLabel h)
      knext <- kStore kaddr
      res <- apply knext addr (dynamic newDelimCtx)
      -- trace ("Restoring handler context for " ++ show h ++ " with\n" ++ show newRetCtx ++ "\n" ++ show newDelimCtx ++ "\n") $ return () 
      returnV $ handleEffects res venv bodId h newRetCtx
    KAddr frame ctx _ _ -> do
      knext <- kStore kaddr
      res <- apply knext addr delimCtx
      let newctx = CombinedCtx ctx delimCtx
      returnV $ continue res frame newctx
isHandlerPrimitive :: Name -> Bool
isHandlerPrimitive n =
  n == nameHandle || isClauseName n || n == nameHTag
  || n == nameEvvAt || n == nameMaskAt || isNamePerform n || isClauseName n
  || n == nameLocalVar || n == nameLocalGet || n == nameLocalSet

doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> [Addr] -> VEnv -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
doHandlerPrimitive name n addr arguments venv ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
  extendStore addr (AChangeObj u name (zip (repeat nameNil) arguments))
  returnAddr addr
doHandlerPrimitive name n addr arguments venv ctx u | isNamePerform n = do
  let label = case exprOfCtx u of
        App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 1))
        _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
  AChangeClos select senv <- store (arguments !! 1)
  let DefCNonRec _ _ opName = select
  let opN = newName $ nameLocalQual (getName opName)
  -- trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
  returnOp (DVal label opN u (drop 2 arguments) ctx) (static ctx) FrameDone DFrameDone EndKAddr
doHandlerPrimitive name n addr arguments venv ctx u | n == nameLocalGet = do
  -- trace ("LocalGet: " ++ show name ++ " " ++ show n ++ "\n" ++ show (head arguments)) $ return ()
  if localEff then do
    let [varAddr@(BindingAddr _ varName), _] = arguments
    returnOp (DVal (getName varName) nameLocalGet u [] ctx) (static ctx) FrameDone DFrameDone EndKAddr
  else do
    returnAddr (head arguments)
doHandlerPrimitive name n addr arguments venv ctx u | n == nameLocalSet = do
  let [varAddr@(BindingAddr _ varName), val] = arguments
  -- trace ("LocalSet: " ++ show name ++ " " ++ show n ++ "\n" ++ show args ++ "\n" ++ show arguments) $ return ()
  if localEff then do
    returnOp (DVal (getName varName) nameLocalSet u [val] ctx) (static ctx) FrameDone DFrameDone EndKAddr
  else do
    rebind val varAddr
    extendStore addr changeUnit
    returnAddr addr
doHandlerPrimitive name n addr arguments venv ctx u | n == nameHandle = do
  args <- mapM store arguments
  case args of
    [AChangeObj _ _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] -> do
      let label = case exprOfCtx u of
            App (TypeApp _ [_, _, _, h, _]) _ _ -> labelName h
      d <- dLimit
      m <- mLimit
      -- trace ("OPS " ++ show henv) $ return ()
      bod <- focusBody body
      -- trace ("Applying handle: " ++ show label ++ " with env " ++ show venv) $ return ()
      let newctx = newDelim d m ctx (contextId u) label
      res <- eval bod (limitEnv bodyenv (fvs body)) newctx
      let h = Handler label (arguments !! 1) (Just ret) (Just $ FDollar (arguments !! 2))
      returnV $ handleEffects res venv (contextId bod) h ctx
    _ -> doBottom
doHandlerPrimitive name n addr arguments venv ctx u | n == nameLocalVar = do
  args <- mapM store arguments
  -- trace ("LocalVar: " ++ show name ++ " " ++ show n) $ return ()
  if localEff then do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        let newEnv = M.insert varName ctx env
        bod <- focusBody e
        d <- dLimit
        m <- mLimit
        let newctx = newDelim d m ctx (contextId u) (getName varName)
        res <- eval bod newEnv newctx
        returnV $ handleLocal res venv (contextId bod) varName (head arguments) ctx
  else do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        let newEnv = M.insert varName ctx env
        bod <- focusBody e
        extendStore (fromJust $ lookupEnv varName newEnv) (head args)
        returnV $ eval bod newEnv ctx
localEff = True

doHandleLocal :: HasCallStack => RValue -> VEnv -> ExprContextId -> TName -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
doHandleLocal res venv bodId varName valAddr retCtx = do
  case res of
    ROp dval ctx' frame' dframe' knext -> do
      let kOp = KAddr frame' ctx' dframe' dval
      extendKStore kOp knext
      case dval of
        DVal hName opName oExpr args oCtx | hName == getName varName && opName == nameLocalGet -> do    
          d <- dLimit
          m <- mLimit
          let newRetCtx = addCall m retCtx bodId
          let newDelimCtx = newDelim d m newRetCtx bodId (getName varName)
          res <- apply kOp valAddr (dynamic newDelimCtx)
          returnV $ handleLocal res venv bodId varName valAddr newRetCtx
        DVal hName opName oExpr [newAddr] oCtx | hName == getName varName && opName == nameLocalSet -> do
          extendStore UnitAddr changeUnit
          d <- dLimit
          m <- mLimit
          let newRetCtx = addCall m retCtx bodId
          let newDelimCtx = newDelim d m newRetCtx bodId (getName varName)
          res <- apply kOp newAddr (dynamic newDelimCtx)
          returnV $ handleLocal res venv bodId varName newAddr newRetCtx
        DVal hName opName opExpr args oCtx -> do
          -- trace ("Passing along local operation: " ++ show opName ++ " at local " ++ show varName ++ " searching for " ++ show hName) $ return ()
          let dframe = DFrameLocal venv bodId varName valAddr
          returnOp dval (static retCtx) (FRestoreDelim dframe) dframe kOp
    RVAddr addr -> returnAddr addr

doHandleEffects :: HasCallStack => RValue -> VEnv -> ExprContextId -> Handler -> CombinedCtx -> FixAAMR r s e FixChange
doHandleEffects res venv bodId h@(Handler label hnd mbRet mbFrame) retCtx = do
  case res of
    ROp dval@(DVal hName opName opExpr args oCtx) ctx' frame' dframe' knext -> do
      if hName == label then do
        let kOp = KAddr frame' ctx' dframe' dval
        extendKStore kOp knext
        -- trace ("Evaluating operation: " ++ show opName ++ " at handler " ++ show label) $ return ()
        AChangeObj _ tname hndargs@(_:ops) <- store hnd
        let ops' = map (\(n, a) -> (unmakeOpHidden opName $ nameStem n, a)) ops
        case lookup opName ops' of
          Nothing -> error ("Unwind: Operation " ++ show opName ++ " not found in " ++ show ops')
          Just op -> do
            AChangeObj _ opConName [opAddr] <- store op
            AChangeClos op openv <- store (snd opAddr)
            let params = lamNames op
            opBod <- focusBody op
            let newEnv = foldl (\acc x -> M.insert x retCtx acc) openv params
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (BindingAddr retCtx) params)
            if isTailOpT opConName then do
              res <- eval opBod (limitEnv newEnv (fvs opBod)) retCtx
              returnV $ continue res (FResume ctx' kOp venv h (contextId opBod)) retCtx
            else if isNeverOp opConName then do
              returnV $ eval opBod (limitEnv newEnv (fvs opBod)) retCtx
            else do
              extendStore (BindingAddr retCtx (last params)) (AChangeKont kOp venv h)
              returnV $ eval opBod (limitEnv newEnv (fvs opBod)) retCtx
      else do
        -- trace ("Allocating new return\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n" ++ show label ++ "," ++ show opName ++ "\n") $ return ()
        let k' = KAddr frame' ctx' dframe' dval
        extendKStore k' knext
        let dframe = DFrame venv bodId h
        returnOp dval (static retCtx) (FRestoreDelim dframe) dframe k'
    res ->
      case mbFrame of
        Just frame -> do
          -- trace ("Continuing after handling effects\n" ++ show retCtx ++ "\n") $ return ()
          returnV $ continue res frame retCtx
        Nothing -> return $ RV res

branchMatch :: Branch -> Addr -> FixAAMR r s e (Maybe (Bindings r s e))
branchMatch branch addr =
  patMatch (head $ branchPatterns branch) addr

type Bindings r s e = (M.Map TName (Addr -> FixAAMR r s e ()), AChangeTree)

data AChangeTree = 
  TChangeV Addr
  | TChangeLit LiteralChangeX
  | TChangeCon (M.Map Name AChangeTree) 

rebind :: Addr -> Addr -> FixAAMR r s e ()
rebind oldAddr newAddr =
  if oldAddr == newAddr then return ()
  else
    each [do
            v <- store oldAddr
            extendStore newAddr v
            doBottom ,
          return ()]

patMatch :: Pattern -> Addr -> FixAAMR r s e (Maybe (Bindings r s e))
patMatch (PatVar name rest) addr = do
  match <- patMatch rest addr
  case match of
    Just (rebinds, values) -> return $ Just (M.insert name (\newAddr -> rebind addr newAddr) rebinds, values)
    Nothing -> return Nothing
patMatch PatWild addr = return $ Just (M.empty, TChangeV addr)
patMatch plit@(PatLit _) addr = do
  v <- store addr
  case v of
    AChangeLit litChange ->
      if patSubsumedX plit litChange then return $ Just (M.empty, TChangeLit litChange)
      else return Nothing
    _ -> return Nothing
patMatch (PatCon nm pats _ _ _ _ _ _) addr = do
  -- TODO: Early catch of wrong type
  v <- store addr
  case v of
    AChangeObj _ name args ->
      if name == nm then do
        let patArgs = zip pats (map snd args)
        matches <- mapM (uncurry patMatch) patArgs
        if all isJust matches then
          return $ Just (M.unions (map (fst . fromJust) matches), TChangeCon (M.fromList (zip (map fst args) (map (snd . fromJust) matches))))
        else return Nothing
      else return Nothing
    AChangeConstr con params ->
      case exprOfCtx con of
        Con conName _ _ ->
         if null pats && nm == conName then return (Just (M.empty, TChangeCon M.empty))
         else return Nothing
    _ -> return Nothing