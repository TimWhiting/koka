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
import Common.Failure (HasCallStack, assertion)
import Type.Type (splitFunType, typeAny, splitFunScheme, Effect, typeTotal, effectExtend, extractEffectExtend, labelName)
import Control.Monad (foldM, zipWithM, zipWithM_)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)
import Type.Pretty (defaultEnv, ppType)
import Lib.PPrint (hcat, tupled, vcat, text)
import Common.File (startsWith, endsWith)
import Syntax.Syntax (ValueBinder(binderName))
import Data.List (intercalate)
import Data.Either (isRight, fromRight)

doStep :: HasCallStack => FixInput -> FixAAMR r s e FixChange
doStep i =
  memo i $ do
    case i of
      VStore UnitAddr -> return $ SV changeUnit
      VStore addr -> error ("Value not found in store :" ++ show addr)
      KStore addr -> if addr == EndKAddr then return $ KV EndKAddr else error ("Continuation not found in store :" ++ show addr)
      Step (CEval expr venv ctx) -> doEval expr venv ctx
      Step (CContinue a b c) -> doDoContinue a b c
      Step (CApply kaddr addr ctx) -> doApply kaddr addr ctx
      Step (CHandleEffects res venv bodId hnd retCtx) -> doHandleEffects res venv bodId hnd retCtx
      Step (CHandleLocal res venv bodId varName valAddr retCtx) -> doHandleLocal res venv bodId varName valAddr retCtx

extendStore :: Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  -- case addr of
    -- BindImplicitAddr{} -> return ()
    -- ConImplicitAddr{} -> return ()
    -- _ -> trace ("Extending store: " ++ show addr ++  " with " ++ show v) $ return ()
  lift $ push (VStore addr) (SV v)
extendKStore :: Addr -> Addr -> FixAAMR r e s ()
extendKStore addr v = do
  -- trace ("Extending KStore: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (KStore addr) (KV v)

store :: HasCallStack => Addr -> FixAAMR r s e AChange
store addr = do
  SV res <- doStep (VStore addr)
  return res
kStore :: HasCallStack => Addr -> FixAAMR r s e Addr
kStore addr = do
  KV res <- doStep (KStore addr)
  return res

unreturnV :: FixAAMR r s e FixChange -> FixAAMR r s e RValue
unreturnV f = do
  RV r <- f
  return r
returnV :: FixAAMR r s e RValue -> FixAAMR r s e FixChange
returnV f = RV <$> f
eval :: HasCallStack => ExprContext -> VEnv -> CombinedCtx -> FixAAMR r s e RValue
eval expr venv ctx = unreturnV $ doStep $ Step (CEval expr venv ctx)
apply :: HasCallStack => Addr -> Addr -> DynamicCtx -> FixAAMR r s e RValue
apply kaddr addr ctx = unreturnV $ doStep $ Step (CApply kaddr addr ctx)
doContinue a b c = doStep $ Step (CContinue a b c)
handleEffects :: HasCallStack => RValue -> VEnv -> Call -> Handler -> CombinedCtx -> FixAAMR r s e RValue
handleEffects res venv bodId hnd retCtx = unreturnV $ doStep $ Step (CHandleEffects res venv bodId hnd retCtx)
handleLocal :: HasCallStack => RValue -> VEnv -> Call -> TName -> Addr -> CombinedCtx -> FixAAMR r s e RValue
handleLocal res venv bodId varName valAddr retCtx = unreturnV $ doStep $ Step (CHandleLocal res venv bodId varName valAddr retCtx)

returnConst :: VEnv -> CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e FixChange
returnConst env ctx expr v = RV . RVAddr <$> allocConst env ctx expr v
returnOp :: DelimitedVal -> StaticCtx -> Frame -> Addr -> FixAAMR r s e FixChange
returnOp dval ctx frame kaddr = return $ RV $ ROp dval ctx frame DFrameDone kaddr
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
        Lit{} -> True
        Con{} -> True
        -- Lam{} -> True
        TypeApp e _ -> isSimpleExpr e
        TypeLam _ e -> isSimpleExpr e
        App (Var nm _) _ _ |  getName nm `elem` [nameHTag, nameEvvAt, nameSSizeT] -> True
        App (TypeApp (Var nm _) _) _ _ | isConstructorName (getName nm) || getName nm `elem` [nameHTag, nameEvvAt, nameSSizeT] -> True
        App (App (TypeApp (Var nm _) _) [e] _) _ _ -> getName nm == nameEffectOpen
        -- Var{} -> True
        -- App e _ _ -> isSimpleExpr e
        _ -> False -- Essentially just Let / Case
      process x = if not open && not (isSimpleExpr (exprOfCtx expr)) then do
                    -- analysisLog ("Evaluating " ++ showCtxExpr expr)
                    -- analysisLog ("Evaluating: " ++ showCtxExpr expr ++ ":" ++ show ctx ++ " with env " ++ showEnv venv)
                    v <- x
                    -- trace ("Result: " ++ showCtxExpr expr ++ ":" ++ show ctx ++ " with env " ++ show venv ++ "\n" ++ show v) $ return ()
                    return v
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
      doContinue res (FMask (contextId expr)) ctx
    App (TypeApp (Var name _) _) [f] _ | getName name == nameMaskBuiltin -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f venv ctx
      doContinue res (FMask (contextId expr)) ctx
    Con tn _ _ -> do
      let params = case splitFunScheme (typeOf tn) of
                      Just (_, params, _, _) -> map fst params
                      Nothing -> []
      let name = case exprOfCtx expr of
                    Con n _ _ -> n
                    _ -> error "Expected a constructor"
      -- trace ("Con: " ++ show tn ++ " with params: " ++ show params) $ return ()
      let constr = AChangeConstr (getName name) params
      returnConst venv ctx expr constr
    Var name _ -> do
      if isPrimitive name && not (isTrickyPrimitive name) then do
        -- trace ("Primitive " ++ show name) $ return ()
        returnConst venv ctx expr (AChangePrim (getName name))
      else if qualifier (getName name) == nameCoreHnd then
        error ("Unexpected handler library name in DMCFA: " ++ show name)
      else case lookupEnv name venv of
        Just addr -> returnAddr addr
        Nothing -> do
          -- trace ("Evaluating external: " ++ show name ++ " " ++ show (ppContextPath expr)) $ return ()
          res <- bindExternal (equalPrimitive name)
          case res of
            Just expr -> do
              c <- startCombinedCtx
              returnV $ eval expr M.empty c
            Nothing -> error ("Variable not found: " ++ show name)
    Lit l -> returnConst venv ctx expr (injLit (contextId expr) l)
    Lam{} -> returnConst venv ctx expr (AChangeClos expr venv)
    App _ args _ -> doApp args
    Let dgs _ -> doLet dgs
    Case _ brs -> doCase brs
    TypeApp{} -> do
      e <- focusChild 0 expr
      returnV $ eval e venv ctx
    TypeLam _ Lam{} -> returnConst venv ctx expr (AChangeClos expr venv)
    TypeLam _ (App _ args _) -> doApp args
    TypeLam _ (Let args _) -> doLet args
    TypeLam _ (Case _ brs) -> doCase brs
    TypeLam _ _ -> do --(TypeApp Var{} _)
      childs <- childrenContexts expr
      -- trace ("TypeLam: " ++ show (map contextId childs)) $ return ()
      e <- focusChild 0 expr
      returnV $ eval e venv ctx
    -- TypeLam _ e -> do
    --   trace ("TypeLam not handled yet: " ++ show e) $ doBottom
  where
    doCase brs = do
          s <- focusScrutinee expr
          branches <- mapM (\i -> focusBranch i expr) [0..length brs - 1]
          res <- eval s (limitEnv venv (fvs s)) ctx
          doContinue res (FScrut expr branches venv) ctx
    doLet dgs = do
          child <- childrenContexts expr
          -- trace ("LetChildren: " ++ intercalate "\n" (map show child)) $ return ()
          bind <- focusLetDefBinding 0 0 expr
          let defGroup = head dgs
          let newEnv = foldl (\acc x -> if defTName x `S.member` S.unions (map (fv . defExpr) (defsOf defGroup)) then extendEnv acc (ctx, contextId expr) (defTName x) else acc) venv (defsOf defGroup)
          let defName = defTName (defOfCtx bind)
          -- trace ("Let binding: " ++ show defName ++ " in " ++ showEnv newEnv) $ return ()
          res <- eval bind (limitEnv newEnv (S.insert defName (fvs bind))) ctx
          doContinue res (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr newEnv) ctx
    doApp args = do
          f <- focusFun expr
          argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
          -- trace ("Applying function: " ++ show f ++ " to args: " ++ show argExprs ++ " with env " ++ show venv) $ return ()
          res <- eval f (limitEnv venv (fvs f)) ctx
          doContinue res (FApp (length args) argExprs [] expr venv) ctx

doDoContinue :: HasCallStack => RValue -> Frame -> CombinedCtx -> FixAAMR r s e FixChange
doDoContinue res frame ctx =
  case res of
    ROp dval ctx' frame' dframe knext -> do
      -- trace ("Capturing frame: " ++ show frame) $ do
      let k' = KAddr frame' ctx' dframe dval
      extendKStore k' knext
      returnOp dval (static ctx) frame k'
    RVAddr addr ->
      -- trace ("Continuing: with frame " ++ show frame) $ do
      case frame of
          FrameDone _ -> returnAddr addr
          FMask _ -> do
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
                      let newEnv = foldl (\acc x -> M.insert x (newCtx, contextId cexpr) acc) cenv args
                      -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show args ++ " in " ++ showEnv newEnv) $ return ()
                      zipWithM_ (\a p -> do
                        val <- store p
                        extendStore (fromJust $ lookupEnv a newEnv) val) args arguments
                      returnV $ eval body (limitEnv newEnv (fvs body)) newCtx
                    AChangePrim name -> do
                      let retAddr = BindImplicitAddr ctx venv uApp
                      if not (isHandlerPrimitive name) then do
                        args <- mapM store arguments
                        res <- doPrimitive name args ctx uApp store extendStore
                        extendStore retAddr res
                        returnAddr retAddr
                      else doHandlerPrimitive name retAddr arguments venv ctx eApp
                    AChangeConstr name params -> do
                      let retAddr = BindImplicitAddr ctx venv uApp
                      let conParams = map (\nm -> ConImplicitAddr nm ctx uApp) params
                      zipWithM_ rebind arguments conParams
                      extendStore retAddr (AChangeObj name (zip params conParams))
                      -- extendStore addr (AChangeObj con name (zip params arguments))
                      returnAddr retAddr
                    AChangeKont kx henv hnd -> do
                      m <- mLimit
                      d <- dLimit
                      let newCtx = addCall m ctx uApp
                          newDynCtx = addDelim d newCtx (CallApp uApp) (hLabel hnd)
                      -- trace ("Applying continuation\n" ++ show uApp ++ "\n" ++ show newCtx ++ "\n" ++ show newDynCtx) $ return () -- ++ "for\n" ++
                      res <- apply kx addr newDynCtx
                      returnV $ handleEffects res henv (CallApp uApp) hnd newCtx
                    _ -> do
                      trace ("Applying non function: " ++ show res) doBottom
              next:rest -> do
                -- trace ("Next " ++ show next) $ return ()
                ret <- eval next (limitEnv venv (fvs next)) ctx
                doContinue ret (FApp n rest (res ++ [addr]) eApp venv) ctx
          FLet groupIdx numGroups bindingIdx numBindings name resolved u venv -> do
            -- trace ("Applying Let " ++ show ctx ++ " env " ++ show venv ++ " " ++ show (lookupEnv name venv)) $ return ()
            let env' =
                  -- if isJust (lookupEnv name venv) then
                  --   assertion ("Rebinding name in let: " ++ show name ++ " from " ++ show (fromJust (lookupEnv name venv)) ++ " to " ++ show (ctx, contextId u) ++ " in " ++ show u)
                  --     (fromJust (M.lookup name venv) == (ctx, contextId u))
                  --   venv
                  -- else
                    M.insert name (ctx, contextId u) venv -- We need to override the old name binding (in case it was in a different context)

            rebind addr (fromJust $ lookupEnv name env')
            -- trace ("Applying Let " ++ show ctx ++ " env " ++ show env'++ " " ++ show (lookupEnv name env')) $ return ()
            -- trace ("Binding " ++ show name ++ " to " ++ show res ++ " in " ++ showEnv venv ++ " new env " ++ showEnv env') $ return ()
            -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
            if isLetDefBindingFinished groupIdx bindingIdx u then do
              -- trace ("Let group finished: " ++ show groupIdx ++ " of " ++ show numGroups) $ return ()
              body <- focusLetBod u
              returnV $ eval body (limitEnv env' (fvs body)) ctx
            else do
              -- trace ("Let group next: " ++ show groupIdx ++ ", " ++ show bindingIdx) $ return ()
              next <- focusNextLetDefBinding groupIdx bindingIdx u
              let nextFrame = nextLetFrame frame{env=env'} ctx
              ret <- eval next (env nextFrame) ctx
              doContinue ret nextFrame ctx
          FScrut parent branches env -> do
            let recur [] _ = doBottom
                recur ((branch, br):branches) tree = do
                  match <- branchMatch br branch tree env ctx
                  case match of
                    Right (bindings, matchTree) -> do
                      let newEnv = foldl (\acc tname -> M.insert tname (ctx, contextId br) acc) env (M.keys bindings)
                      mapM_ (\(tname, extend) ->
                        extend (fromJust $ lookupEnv tname newEnv)
                        ) (M.toList bindings)
                      each [
                          do
                            body <- focusBranchExpr br
                            returnV $ eval body (limitEnv newEnv (fvs body)) ctx,
                          if definitelyMatched matchTree then doBottom
                          else recur branches matchTree
                       ]
                    Left newTree -> recur branches newTree
            case exprOfCtx parent of
              Case _ pats -> recur (zip pats branches) (TChangeV addr)
          FDollar _ va -> do
            res <- store va
            case res of
              AChangeClos cexpr cenv -> do
                  body <- focusBody cexpr
                  let [arg] = lamNames cexpr
                  let newEnv = M.insert arg (ctx, contextId cexpr) cenv
                  v <- store addr
                  extendStore (fromJust $ lookupEnv arg newEnv) v
                  returnV $ eval body (limitEnv newEnv (fvs body)) ctx
          FResume retCtx kont venv hnd u -> do
            m <- mLimit
            d <- dLimit
            let newRetCtx = addCall m ctx u
                newDelimCtx = addDelim d newRetCtx (CallApp u) (hLabel hnd)
            -- trace ("Applying continuation " ++ show (contextId u) ++ " " ++ show henv ) $ return () -- ++ "for\n" ++ 
            AChangeKont kaddr _ _ <- store kont
            res <- apply kaddr addr newDelimCtx
            returnV $ handleEffects res venv (CallApp u) hnd newRetCtx
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
      let newRetCtx = addCallRaw m newCtx bodId
      let newDelimCtx = newDelim d m newRetCtx bodId (getName varName)
      knext <- kStore kaddr
      res <- apply knext addr (dynamic newDelimCtx)
      returnV $ handleLocal res venv bodId varName varAddr newRetCtx
    KAddr (FRestoreDelim (DFrame venv bodId h)) ctx _ _ -> do
      let newCtx = CombinedCtx ctx delimCtx
      d <- dLimit
      m <- mLimit
      let newRetCtx = addCallRaw m newCtx bodId
      let newDelimCtx = newDelim d m newRetCtx bodId (hLabel h)
      knext <- kStore kaddr
      res <- apply knext addr (dynamic newDelimCtx)
      -- trace ("Restoring handler context for " ++ show h ++ " with\n" ++ show newRetCtx ++ "\n" ++ show newDelimCtx ++ "\n") $ return () 
      returnV $ handleEffects res venv bodId h newRetCtx
    KAddr frame ctx _ _ -> do
      knext <- kStore kaddr
      res <- apply knext addr delimCtx
      let newctx = CombinedCtx ctx delimCtx
      doContinue res frame newctx
isHandlerPrimitive :: Name -> Bool
isHandlerPrimitive n =
  n == nameHandle || isClauseName n || n == nameHTag
  || n == nameEvvAt || n == nameMaskAt || isNamePerform n || isClauseName n
  || n == nameLocalVar || n == nameLocalGet || n == nameLocalSet

doHandlerPrimitive :: HasCallStack => Name -> Addr -> [Addr] -> VEnv -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
doHandlerPrimitive n addr arguments venv ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
  extendStore addr (AChangeObj n (zip (repeat nameNil) arguments))
  returnAddr addr
doHandlerPrimitive n addr arguments venv ctx u | isNamePerform n = do
  let label = case exprOfCtx u of
        App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 1))
        _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
  AChangeClos select senv <- store (arguments !! 1)
  let DefCNonRec _ _ opName = select
  let opN = newName $ nameLocalQual (getName opName)
  -- trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
  returnOp (DVal label opN u (drop 2 arguments) ctx) (static ctx) (FrameDone (contextId u)) EndKAddr
doHandlerPrimitive n addr arguments venv ctx u | n == nameLocalGet = do
  -- trace ("LocalGet: " ++ show name ++ " " ++ show n ++ "\n" ++ show (head arguments)) $ return ()
  if localEff then do
    let [varAddr@(BindingAddr _ varName _), _] = arguments
    returnOp (DVal (getName varName) nameLocalGet u [] ctx) (static ctx) (FrameDone (contextId u)) EndKAddr
  else do
    returnAddr (head arguments)
doHandlerPrimitive n addr arguments venv ctx u | n == nameLocalSet = do
  let [varAddr@(BindingAddr _ varName _), val] = arguments
  -- trace ("LocalSet: " ++ show name ++ " " ++ show n ++ "\n" ++ show args ++ "\n" ++ show arguments) $ return ()
  if localEff then do
    returnOp (DVal (getName varName) nameLocalSet u [val] ctx) (static ctx) (FrameDone (contextId u)) EndKAddr
  else do
    rebind val varAddr
    extendStore addr changeUnit
    returnAddr addr
doHandlerPrimitive n addr arguments venv ctx u | n == nameHandle = do
  args <- mapM store arguments
  case args of
    [AChangeObj _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] -> do
      let label = case exprOfCtx u of
            App (TypeApp _ [_, _, _, h, _]) _ _ -> labelName h
      d <- dLimit
      m <- mLimit
      -- trace ("OPS " ++ show henv) $ return ()
      bod <- focusBody body
      -- trace ("Applying handle: " ++ show label ++ " with env " ++ showEnv venv) $ return ()
      let newctx = newDelim d m ctx (CallApp $ contextId u) label
      res <- eval bod (limitEnv bodyenv (fvs body)) newctx
      let h = Handler label (arguments !! 1) (Just ret) (Just $ FDollar (contextId u) (arguments !! 2))
      returnV $ handleEffects res venv (CallApp $ contextId bod) h ctx
    _ -> doBottom
doHandlerPrimitive n addr arguments venv ctx u | n == nameLocalVar = do
  args <- mapM store arguments
  -- trace ("LocalVar: " ++ show name ++ " " ++ show n) $ return ()
  if localEff then do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        let newEnv = M.insert varName (ctx, contextId e) env
        bod <- focusBody e
        d <- dLimit
        m <- mLimit
        let newctx = newDelim d m ctx (CallApp $ contextId u) (getName varName)
        rebind UnitAddr (fromJust $ lookupEnv varName newEnv)
        res <- eval bod newEnv newctx
        returnV $ handleLocal res newEnv (CallApp $ contextId bod) varName (head arguments) ctx
  else do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        let newEnv = M.insert varName (ctx, contextId e) env
        bod <- focusBody e
        extendStore (fromJust $ lookupEnv varName newEnv) (head args)
        returnV $ eval bod newEnv ctx
localEff = True

doHandleLocal :: HasCallStack => RValue -> VEnv -> Call -> TName -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
doHandleLocal res venv bodId varName valAddr retCtx = do
  case res of
    ROp dval ctx' frame' dframe' knext -> do
      let kOp = KAddr frame' ctx' dframe' dval
      extendKStore kOp knext
      case dval of
        DVal hName opName oExpr args oCtx | hName == getName varName && opName == nameLocalGet -> do
          res <- apply kOp valAddr (dynamic retCtx)
          returnV $ handleLocal res venv bodId varName valAddr retCtx
        DVal hName opName oExpr [newAddr] oCtx | hName == getName varName && opName == nameLocalSet -> do
          -- v <- store newAddr
          extendStore UnitAddr changeUnit
          v <- store newAddr
          d <- dLimit
          m <- mLimit
          let newRetCtx = addCallRaw m retCtx (CtxId $ vcontextId v)
          let newDelimCtx = newDelim d m newRetCtx (CtxId $ vcontextId v) (getName varName)
          res <- apply kOp UnitAddr (dynamic newDelimCtx)
          returnV $ handleLocal res venv (CtxId $ vcontextId v) varName newAddr newRetCtx
        DVal hName opName opExpr args oCtx -> do
          -- trace ("Passing along local operation: " ++ show opName ++ " at local " ++ show varName ++ " searching for " ++ show hName) $ return ()
          let dframe = DFrameLocal venv bodId varName valAddr
          returnOp dval (static retCtx) (FRestoreDelim dframe) kOp
    RVAddr addr -> returnAddr addr

doHandleEffects :: HasCallStack => RValue -> VEnv -> Call -> Handler -> CombinedCtx -> FixAAMR r s e FixChange
doHandleEffects res venv bodId h@(Handler label hnd mbRet mbFrame) retCtx = do
  case res of
    ROp dval@(DVal hName opName opExpr args oCtx) ctx' frame' dframe' knext -> do
      if hName == label then do
        let kOp = KAddr frame' ctx' dframe' dval
        extendKStore kOp knext
        -- trace ("Evaluating operation: " ++ show opName ++ " at handler " ++ show label) $ return ()
        AChangeObj tname hndargs@(_:ops) <- store hnd
        let ops' = map (\(n, a) -> (unmakeOpHidden opName $ nameStem n, a)) ops
        case lookup opName ops' of
          Nothing -> error ("Unwind: Operation " ++ show opName ++ " not found in " ++ show ops' ++ " " ++ show hName ++ " " ++ show hnd)
          Just op -> do
            AChangeObj opConName [opAddr] <- store op
            AChangeClos op openv <- store (snd opAddr)
            let params = lamNames op
            opBod <- focusBody op
            let newEnv = foldl (\acc x -> M.insert x (retCtx, contextId op) acc) openv params
            -- trace (" Operation: " ++ show opName ++ " with params " ++ show params ++ " and args " ++ show args ++ " in " ++ showEnv newEnv) $ return ()
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (\n -> BindingAddr retCtx n (contextId op)) params)
            if isTailOp opConName then do
              res <- eval opBod (limitEnv newEnv (fvs opBod)) retCtx
              let kaddr = BindKImplicitAddr retCtx venv (contextId op)
              extendStore kaddr (AChangeKont kOp venv h)
              doContinue res (FResume ctx' kaddr venv h (contextId opBod)) retCtx
            else if isNeverOp opConName then do
              returnV $ eval opBod (limitEnv newEnv (fvs opBod)) retCtx
            else do
              extendStore (BindingAddr retCtx (last params) (contextId op)) (AChangeKont kOp venv h)
              returnV $ eval opBod (limitEnv newEnv (fvs opBod)) retCtx
      else do
        -- trace ("Allocating new return\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n" ++ show label ++ "," ++ show opName ++ "\n") $ return ()
        let k' = KAddr frame' ctx' dframe' dval
        extendKStore k' knext
        let dframe = DFrame venv bodId h
        returnOp dval (static retCtx) (FRestoreDelim dframe) k'
    res ->
      case mbFrame of
        Just frame -> do
          -- trace ("Continuing after handling effects\n" ++ show retCtx ++ "\n") $ return ()
          doContinue res frame retCtx
        Nothing -> return $ RV res

branchMatch :: ExprContext -> Branch -> AChangeTree -> VEnv -> CombinedCtx -> FixAAMR r s e (Either AChangeTree (Bindings r s e) )
branchMatch branchCtx branch addr env ctx = do
  match <- patMatch (head $ branchPatterns branch) addr
  case match of
    Left tree -> return $ Left tree
    Right (bindings, tree) ->
      if isExprTrue (guardTest $ head (branchGuards branch)) then return $ Right (bindings, tree)
      else do
        guard <- focusGuardExpr branchCtx
        let newEnv = foldl (\acc tname -> M.insert tname (ctx, contextId branchCtx) acc) env (M.keys bindings)
        mapM_ (\(tname, extend) ->
          extend (fromJust $ lookupEnv tname newEnv)
          ) (M.toList bindings)
        RVAddr a <- eval guard newEnv ctx
        v <- store a
        case v of
          AChangeConstr conName _ ->
            if conName == nameTrue then
                return $ Right (bindings, tree)
            else return $ Left tree
          _ -> return $ Left tree

type Bindings r s e = (M.Map TName (Addr -> FixAAMR r s e ()), AChangeTree)

data AChangeTree =
  TChangeV Addr
  | TChangeLit Addr LiteralChangeX
  | TChangeCon Addr AChange (M.Map Name AChangeTree)
  | TChangePartialCon Addr AChange

-- Assuming that the tree is from the Bindings then it definitely matches this pattern, i.e., all literals are fully matched
definitelyMatched :: AChangeTree -> Bool
definitelyMatched (TChangeV _) = True
definitelyMatched (TChangeLit _ (LiteralChangeCharX LChangeTop)) = False
definitelyMatched (TChangeLit _ (LiteralChangeIntX LChangeTop)) = False
definitelyMatched (TChangeLit _ (LiteralChangeFloatX LChangeTop)) = False
definitelyMatched (TChangeLit _ (LiteralChangeStringX LChangeTop)) = False
definitelyMatched (TChangeLit _ _) = True
definitelyMatched (TChangeCon _ _ m) = all definitelyMatched (M.elems m)
definitelyMatched (TChangePartialCon _ _) = True

rebind :: HasCallStack => Addr -> Addr -> FixAAMR r s e ()
rebind oldAddr newAddr =
  if oldAddr == newAddr then return ()
  else
    each [do
            v <- store oldAddr
            extendStore newAddr v
            doBottom ,
          return ()]

addrOfTree :: AChangeTree -> Addr
addrOfTree (TChangeV addr) = addr
addrOfTree (TChangeLit addr _) = addr
addrOfTree (TChangeCon addr _ _) = addr
addrOfTree (TChangePartialCon addr _) = addr

changeOfTree :: AChangeTree -> FixAAMR r s e AChange
changeOfTree (TChangeV addr) = store addr
changeOfTree (TChangeLit _ litChange) = return $ AChangeLit litChange
changeOfTree (TChangeCon _ con _) = return con
changeOfTree (TChangePartialCon _ con) = return con
argsOfChange :: AChangeTree -> [AChangeTree]
argsOfChange (TChangeCon _ _ args) = M.elems args
argsOfChange _ = []
treeUnion :: AChangeTree -> AChangeTree -> AChangeTree
treeUnion (TChangeV addr) tree2 = tree2 -- Left terminates, take right
treeUnion tree1 (TChangeV addr) = tree1 -- Right terminates, take left
treeUnion (TChangeCon addr con args) TChangePartialCon{} = TChangeCon addr con args -- Prefer the more specific tree
treeUnion TChangePartialCon{} (TChangeCon addr con args) = TChangeCon addr con args -- Prefer the more specific tree
treeUnion (TChangeCon addr1 con1 args1) (TChangeCon addr2 con2 args2) = -- Merge the arguments
  TChangeCon addr1 con1 (M.unionWith treeUnion args1 args2)
treeUnion t1 t2 = t1 -- Prefer the first tree (doesn't matter for literals)

getTree :: Either AChangeTree (Bindings r s e) -> AChangeTree
getTree (Left tree) = tree
getTree (Right (_, tree)) = tree

patMatch :: Pattern -> AChangeTree -> FixAAMR r s e (Either AChangeTree (Bindings r s e))
patMatch (PatVar name rest) tree = do
  match <- patMatch rest tree
  case match of -- TODO: We should reallocate / rebind only the parts of the address that match the tree
    Right (rebinds, values) -> return $ Right (M.insert name (\newAddr -> rebind (addrOfTree tree) newAddr) rebinds, values)
    Left tree -> return $ Left tree
patMatch PatWild tree = return $ Right (M.empty, tree)
patMatch plit@(PatLit _) tree = do
  v <- changeOfTree tree
  case v of
    AChangeLit litChange ->
      if patSubsumedX plit litChange then return $ Right (M.empty, TChangeLit (addrOfTree tree) litChange)
      else return (Left tree)
    _ -> return (Left tree)
patMatch (PatCon nm pats _ _ _ _ _ _) (TChangeLit addr l) = return $ Left (TChangeLit addr l)
patMatch pcon@(PatCon nm pats _ _ _ _ _ _) tree = do
  let newArgs args [] = map (TChangeV . snd) args -- take the rest as is
      newArgs (_:args) (n:rest) = n : newArgs args rest -- prefer known tree elements
  -- trace ("Matching pattern " ++ show pcon ++ " against tree at " ++ show (addrOfTree tree)) $ return ()
  -- TODO: Early catch of wrong type
  v <- changeOfTree tree
  case v of
    AChangeObj name args ->
      -- trace ("Pattern constructor " ++ show nm ++ " against object " ++ show name ++ " with args " ++ show (map fst args)) $ return () >>
      if name == getName nm then do
        let patArgs = zip pats (newArgs args (argsOfChange tree))
        matches <- mapM (uncurry patMatch) patArgs
        let newTree = treeUnion tree $ TChangeCon (addrOfTree tree) v (M.fromList (zip (map fst args) (map getTree matches)))
        if all isRight matches then
          return $ Right (M.unions (map (\(Right match) -> fst match) matches), newTree)
        else return $ Left newTree
      else return $ Left tree
    AChangeConstr conName params ->
      -- trace ("Pattern constructor " ++ show nm ++ " against object " ++ show con) $ return () >>
      if null pats && getName nm == conName then return (Right (M.empty, TChangePartialCon (addrOfTree tree) v))
      else return $ Left tree
    _ -> return $ Left tree