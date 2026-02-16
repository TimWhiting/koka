{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use map with tuple-section" #-}
module Core.FlowAnalysis.Full.DMCFAR2.DMCFA where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Full.DMCFAR2.AbstractValue
import Core.FlowAnalysis.Full.DMCFAR2.Monad
import Core.FlowAnalysis.Full.DMCFAR2.Primitives
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
import Data.Either (isRight, fromRight)

-- TERMINATION GUARANTEE:
-- The analysis terminates because:
-- 1. FixInput (the memoization key) has finite state space (documented in AbstractValue.hs)
-- 2. All recursive analysis calls go through doStep (memoization boundary)
-- 3. Results form a lattice with finite height (changes propagate upward via FixChange)
-- 4. Helper functions (patMatch, branchMatch) recurse on finite structures (source program syntax)
-- 5. No infinite loops exist outside memoization (all recursion bounded by program structure)
doStep :: HasCallStack => FixInput -> FixAAMR r s e FixChange
doStep i =
  memo i $ do
    case i of
      VStore UnitAddr -> return $ SV changeUnit
      VStore addr -> error ("Value not found in store :" ++ show addr)
      KStore addr -> if addr == EndKAddr then return $ KV (FCount, EndKAddr) else error ("Continuation not found in store :" ++ show addr)
      Step (CEval expr venv) -> doEval expr venv
      Step (CApply kaddr addr ctx) -> doApply kaddr addr ctx
      Step (CContinue res frame ctx) -> doDoContinue res frame ctx
      Step (CHandleEffects res venv bodId hnd ctx) -> doHandleEffects res venv bodId hnd ctx
      Step (CHandleLocal res venv bodId varName valAddr ctx) -> doHandleLocal res venv bodId varName valAddr ctx

extendStore :: Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  -- case addr of
    -- BindImplicitAddr{} -> return ()
    -- ConImplicitAddr{} -> return ()
    -- _ -> trace ("Extending store: " ++ show addr ++  " with " ++ show v) $ return ()
  lift $ push (VStore addr) (SV v)
extendKStore :: Addr -> Frame -> Addr -> FixAAMR r e s ()
extendKStore addr f v = do
  -- trace ("Extending KStore: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (KStore addr) (KV (f,v))

store :: HasCallStack => Addr -> FixAAMR r e s AChange
store addr = do
  SV res <- doStep (VStore addr)
  return res

kStore :: HasCallStack => Addr -> FixAAMR r e s (Frame, Addr)
kStore addr = do
  KV res <- doStep (KStore addr)
  return res

unreturnV :: FixAAMR r s e FixChange -> FixAAMR r s e RValue
unreturnV f = do
  RV r <- f
  return r
returnV :: FixAAMR r s e RValue -> FixAAMR r s e FixChange
returnV f = RV <$> f
eval :: HasCallStack => ExprContext -> VEnv -> FixAAMR r s e RValue
eval expr venv = unreturnV $ doStep $ Step (CEval expr venv)
apply :: HasCallStack => Addr -> Addr -> DynamicCtx -> FixAAMR r s e RValue
apply kaddr addr ctx = unreturnV $ doStep $ Step (CApply kaddr addr ctx)
doContinue a b c = doStep $ Step (CContinue a b c)

handleEffects :: HasCallStack => RValue -> VEnv -> Call -> Handler -> CombinedCtx -> FixAAMR r s e RValue
handleEffects res venv bodId hnd ctx = unreturnV $ doStep $ Step (CHandleEffects res venv bodId hnd ctx)
handleLocal :: HasCallStack => RValue -> VEnv -> Call -> (ExprContextId, TName) -> Addr -> CombinedCtx -> FixAAMR r s e RValue
handleLocal res venv bodId varName valAddr ctx = unreturnV $ doStep $ Step (CHandleLocal res venv bodId varName valAddr ctx)

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

doEval :: HasCallStack => ExprContext -> VEnv -> FixAAMR r s e FixChange
doEval expr venv = do
  let open = case exprOfCtx expr of
        App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen -> True
        _ -> False
      isSimpleExpr e = case e of
        Var{} -> True
        Lit{} -> True
        Con{} -> True
        -- Lam{} -> True
        TypeApp e _ -> isSimpleExpr e
        TypeLam _ e -> isSimpleExpr e
        App (Var nm _) _ _ |  getName nm `elem` [nameHTag, nameEvvAt, nameSSizeT] -> True
        App (TypeApp (Var nm _) _) _ _ | isConstructorName (getName nm) || getName nm `elem` [nameHTag, nameEvvAt, nameSSizeT] -> True
        App (App (TypeApp (Var nm _) _) [e] _) _ _ -> getName nm == nameEffectOpen
        -- App e _ _ -> isSimpleExpr e
        _ -> False -- Essentially just Let / Case
      process x = if not open && not (isSimpleExpr (exprOfCtx expr)) then do
                    -- analysisLog ("Evaluating: " ++ showCtxExpr expr ++ ": with env " ++ show venv)
                    v <- x
                    -- trace ("Result: " ++ showCtxExpr expr ++ ": with env " ++ show venv ++ "\n" ++ show v) $ return ()
                    return v
                  else x-- trace ("Evaluating: " ++ show expr ++ " in " ++ show (M.toList venv) ++ " : " ++ show ctx) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
   in process $ case exprOfCtx expr of
    App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen || getName name == namePretendDecreasing -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      returnV $ eval f venv
    App (TypeApp (Var name _) _) [_,_,f] _ | getName name == nameMaskAt -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 3 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f venv
      doContinue res (FMask (contextId expr)) (envCtx venv)
    App (TypeApp (Var name _) _) [f] _ | getName name == nameMaskBuiltin -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f venv
      doContinue res (FMask (contextId expr)) (envCtx venv)
    Con tn _ _ -> do
      let params = case splitFunScheme (typeOf tn) of
                      Just (_, params, _, _) -> map fst params
                      Nothing -> []
      let name = case exprOfCtx expr of
                    Con n _ _ -> n
                    _ -> error "Expected a constructor"
      -- trace ("Con: " ++ show tn ++ " with params: " ++ show params) $ return ()
      let constr = AChangeConstr (getName name) params
      returnConst venv (envCtx venv) expr constr
    Var name _ -> do
      if isPrimitive name && not (isTrickyPrimitive name) then do
        -- trace ("Primitive " ++ show name) $ return ()
        returnConst venv (envCtx venv) expr (AChangePrim (getName name))
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
              returnV $ eval expr (c, M.empty)
            Nothing -> trace ("Variable not found: " ++ show name) doBottom
    Lit l -> returnConst venv (envCtx venv) expr (injLit (contextId expr) l)
    Lam{} -> returnConst venv (envCtx venv) expr (AChangeClos expr (limitEnv venv (fvs expr)))
    App _ args _ -> doApp args
    Let dgs _ -> doLet dgs
    Case _ brs -> doCase brs
    TypeApp{} -> do
      e <- focusChild 0 expr
      returnV $ eval e venv
    TypeLam _ Lam{} -> returnConst venv (envCtx venv) expr (AChangeClos expr (limitEnv venv (fvs expr)))
    TypeLam _ (App _ args _) -> doApp args
    TypeLam _ (Let args _) -> doLet args
    TypeLam _ (Case _ brs) -> doCase brs
    TypeLam _ _ -> do --(TypeApp Var{} _)
      childs <- childrenContexts expr
      -- trace ("TypeLam: " ++ show (map contextId childs)) $ return ()
      e <- focusChild 0 expr
      returnV $ eval e venv
    -- TypeLam _ e -> do
    --   trace ("TypeLam not handled yet: " ++ show e) $ doBottom
  where
    doCase brs = do
          s <- focusScrutinee expr
          branches <- mapM (\i -> focusBranch i expr) [0..length brs - 1]
          res <- eval s (limitEnv venv (fvs s))
          doContinue res (FScrut expr branches venv) (envCtx venv)
    doLet dgs = do
          child <- childrenContexts expr
          -- trace ("LetChildren: " ++ intercalate "\n" (map show child)) $ return ()
          bind <- focusLetDefBinding 0 0 expr
          let defGroup = head dgs
          let newEnv = foldl (\acc x -> if defTName x `S.member` S.unions (map (fv . defExpr) (defsOf defGroup)) then extendEnv acc (contextId expr) (defTName x) else acc) venv (defsOf defGroup)
          let defName = defTName (defOfCtx bind)
          -- trace ("Let binding: " ++ show defName ++ " in " ++ show newEnv) $ return ()
          res <- eval bind (limitEnv newEnv (S.insert defName (fvs bind)))
          doContinue res (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr newEnv) (envCtx venv)
    doApp args = do
          f <- focusFun expr
          argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
          -- trace ("Applying function: " ++ show f ++ " to args: " ++ show argExprs ++ " with env " ++ show venv) $ return ()
          res <- eval f (limitEnv venv (fvs f))
          doContinue res (FApp (length args) argExprs [] expr venv) (envCtx venv)

adjustAddr (BindingAddr _ nm u) env' i ectx ctx  = BindingAddr ctx nm u
adjustAddr (BindImplicitAddr _ _ u) env' i ectx ctx = ArgImplicitAddr ctx env' i ectx
adjustAddr (ArgImplicitAddr _ _ _ u) env' i ectx ctx = ArgImplicitAddr ctx env' i ectx
adjustAddr UnitAddr _ _ _ _ = UnitAddr

rebindAll :: HasCallStack => VEnv -> CombinedCtx -> FixAAMR r s e VEnv
rebindAll (oldCtx, vars) ctx = do
  mapM_ (\(var, ctxId) -> rebind (BindingAddr oldCtx var ctxId) (BindingAddr ctx var ctxId)) (M.toList vars)
  return (ctx, vars)

rebindAllAddrs :: HasCallStack => ExprContextId -> [Addr] -> VEnv -> CombinedCtx -> FixAAMR r s e (VEnv, [Addr])
rebindAllAddrs ectx addrs (oldCtx, vars) newCtx = do
  if oldCtx == newCtx then return ((oldCtx, vars), addrs) else do
    let newEnv = (newCtx, vars)
    addrs' <- zipWithM (\i addr -> do
        let newAddr = adjustAddr addr newEnv i ectx newCtx
        rebind addr newAddr
        return newAddr) [0..] addrs
    return (newEnv, addrs')

doDoContinue :: HasCallStack => RValue -> Frame -> CombinedCtx -> FixAAMR r s e FixChange
doDoContinue res frame ctx =
  case res of
    ROp dval ctx' frame' dframe knext -> do
      -- trace ("Capturing frame: " ++ show frame) $ do
      let k' = KAddr frame' ctx' dframe dval
      extendKStore k' frame knext
      returnOp dval (static ctx) frame k'
    RVAddr addr ->
      -- trace ("Continuing: with frame " ++ show frame ++ " in " ++ show ctx) $ do
      case frame of
          FrameDone _ -> returnAddr addr
          FMask _ -> do
            v <- store addr
            case v of
              AChangeClos e env -> do
                bod <- focusBody e
                env' <- rebindAll env ctx
                returnV $ eval bod env'
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
                      env' <- rebindAll cenv newCtx
                      let newEnv = foldl (\acc x -> extendEnv acc (contextId cexpr) x) env' args
                      -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show args) $ return ()
                      zipWithM_ (\a p -> do
                        val <- store p
                        extendStore (fromJust $ lookupEnv a newEnv) val) args arguments
                      returnV $ eval body newEnv
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
                      -- trace ("Applying non function: " ++ show res) 
                      doBottom
              next:rest -> do
                app <- M.lookup uApp . states <$> getState
                -- trace ("Next\n" ++ show next ++ "\n:" ++ show ctx ++ "\n" ++ show app ++ "\n" ++ show venv) $ return ()
                env' <- rebindAll venv ctx
                (env'', addrs') <- rebindAllAddrs uApp (res ++ [addr]) env' ctx
                ret <- eval next (limitEnv env'' (fvs next))
                doContinue ret (FApp n rest addrs' eApp env'') ctx -- TODO: Get all the new addresses for the frame.
          FLet groupIdx numGroups bindingIdx numBindings name resolved u (oldCtx, venv) -> do
            -- trace ("Applying Let " ++ show newctx ++ " env " ++ show venv) $ return ()
            val <- store addr
            env' <- rebindAll (oldCtx, M.delete name venv) ctx
            let newEnv = extendEnv env' (contextId u) name  -- We need to override the old name binding (in case it was in a different context)
            extendStore (fromJust $ lookupEnv name newEnv) val
            -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show venv ) $ return ()
            -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
            if isLetDefBindingFinished groupIdx bindingIdx u then do
              -- trace ("Let group finished: " ++ show groupIdx ++ " of " ++ show numGroups) $ return ()
              body <- focusLetBod u
              returnV $ eval body (limitEnv newEnv (fvs body))
            else do
              -- trace ("Let group old:\n" ++ show frame) $ return ()
              let nextFrame = nextLetFrame frame{env=newEnv} ctx
              -- trace ("Let group next:\n" ++ show nextFrame) $ return ()
              next <- focusNextLetDefBinding groupIdx bindingIdx u
              ret <- eval next (env nextFrame)
              doContinue ret nextFrame ctx
          FScrut parent branches env -> do
            -- Branch matching recursion is bounded by the finite list of branches from source program.
            -- The recur function processes the branches list, which decreases on each recursive call.
            let recur [] _ = doBottom -- error ("NO matching branch found\n" ++ show tree ++ "\n" ++ show parent)
                recur ((branch, br):branches) tree = do
                  match <- branchMatch br branch tree env ctx
                  case match of
                    Right (bindings, matchTree) -> do
                      body <- focusBranchExpr br
                      env' <- rebindAll (limitEnv env (fvs body)) ctx
                      let newEnv = foldl (\acc tname -> extendEnv acc (contextId br) tname) env' (M.keys bindings)
                      mapM_ (\(tname, extend) ->
                        extend (fromJust $ lookupEnv tname newEnv)
                        ) (M.toList bindings)
                      each [
                          do returnV $ eval body (limitEnv newEnv (fvs body)),
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
                  env' <- rebindAll cenv ctx
                  let newEnv = extendEnv env' (contextId cexpr) arg
                  v <- store addr
                  extendStore (fromJust $ lookupEnv arg newEnv) v
                  returnV $ eval body (limitEnv newEnv (fvs body))
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

kAddrFrame :: Addr -> Frame
kAddrFrame (KAddr fr _ _ _) = fr

doApply :: HasCallStack => Addr -> Addr -> DynamicCtx -> FixAAMR r s e FixChange
doApply kaddr addr delimCtx = do
  -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show delimCtx) $ return ()
  -- trace ("Applying: " ++ show k) $ return ()
  case kaddr of
    EndKAddr -> returnAddr addr
    KAddr frame1 ctx _ _ -> do
      (frame, knext) <- kStore kaddr 
      -- if Just frame /= frame0 && frame0 /= Nothing then doBottom
      -- else 
      case frame of 
        FRestoreDelim (DFrameLocal venv bodId (id, varName) varAddr) -> do
          let newCtx = CombinedCtx ctx delimCtx
          d <- dLimit
          m <- mLimit
          let newRetCtx = addCallRaw m newCtx bodId
          let newDelimCtx = newDelim d m newRetCtx bodId (getName varName)
          res <- apply knext addr (dynamic newDelimCtx)
          returnV $ handleLocal res venv bodId (id, varName) varAddr newRetCtx
        FRestoreDelim (DFrame venv bodId h) -> do
          let newCtx = CombinedCtx ctx delimCtx
          d <- dLimit
          m <- mLimit
          let newRetCtx = addCallRaw m newCtx bodId
          let newDelimCtx = newDelim d m newRetCtx bodId (hLabel h)
          res <- apply knext addr (dynamic newDelimCtx)
          -- trace ("Restoring handler context for " ++ show h ++ " with\n" ++ show newRetCtx ++ "\n" ++ show newDelimCtx ++ "\n") $ return () 
          returnV $ handleEffects res venv bodId h newRetCtx
        _ -> do
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
      -- trace ("Applying handle: " ++ show label ++ " with env " ++ show venv) $ return ()
      let newctx = newDelim d m ctx (CallApp $ contextId u) label
      env' <- rebindAll bodyenv newctx
      res <- eval bod env'
      let h = Handler (contextId bod) label (arguments !! 1) (Just ret) (Just $ FDollar (contextId u) (arguments !! 2))
      returnV $ handleEffects res venv (CallApp $ contextId bod) h ctx
    _ -> error ("Malformed handle primitive arguments: " ++ show args)
doHandlerPrimitive n addr arguments venv ctx u | n == nameLocalVar = do
  args <- mapM store arguments
  -- trace ("LocalVar: " ++ show name ++ " " ++ show n) $ return ()
  if localEff then do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        bod <- focusBody e
        d <- dLimit
        m <- mLimit
        let newctx = newDelim d m ctx (CallApp $ contextId u) (getName varName)
        env' <- rebindAll env newctx
        let newEnv = extendEnv env' (contextId e) varName
        rebind UnitAddr (fromJust $ lookupEnv varName newEnv)
        res <- eval bod newEnv
        returnV $ handleLocal res newEnv (CallApp $ contextId bod) (contextId bod, varName) (head arguments) ctx
  else do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        bod <- focusBody e
        env' <- rebindAll env ctx
        let newEnv = extendEnv env' (contextId e) varName
        extendStore (fromJust $ lookupEnv varName newEnv) (head args)
        returnV $ eval bod newEnv
localEff = True

doHandleLocal :: HasCallStack => RValue -> VEnv -> Call -> (ExprContextId, TName) -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
doHandleLocal res venv bodId (id, varName) valAddr retCtx = do
  case res of
    ROp dval ctx' frame' dframe' knext -> do
      case dval of
        DVal hName opName oExpr args oCtx | hName == getName varName && opName == nameLocalGet -> do
          res <- apply knext valAddr (dynamic retCtx)
          returnV $ handleLocal res venv bodId (id, varName) valAddr retCtx
        DVal hName opName oExpr [newAddr] oCtx | hName == getName varName && opName == nameLocalSet -> do
          extendStore UnitAddr changeUnit
          v <- store newAddr
          d <- dLimit
          m <- mLimit
          let newRetCtx = addCallRaw m retCtx (CtxId $ vcontextId v)
          let newDelimCtx = newDelim d m newRetCtx (CtxId $ vcontextId v) (getName varName)
          res <- apply knext UnitAddr (dynamic newDelimCtx)
          returnV $ handleLocal res venv (CtxId $ vcontextId v) (id, varName) newAddr newRetCtx
        DVal hName opName opExpr args oCtx -> do
          -- trace ("Passing along local operation: " ++ show opName ++ " at local " ++ show varName ++ " searching for " ++ show hName) $ return ()
          let kOp = KAddr frame' ctx' dframe' dval
          let dframe = DFrameLocal venv bodId (id, varName) valAddr
          extendKStore kOp (FRestoreDelim dframe) knext
          returnOp dval (static retCtx) (FRestoreDelim dframe) kOp
    RVAddr addr -> returnAddr addr

doHandleEffects :: HasCallStack => RValue -> VEnv -> Call -> Handler -> CombinedCtx -> FixAAMR r s e FixChange
doHandleEffects res venv bodId h@(Handler id label hnd mbRet mbFrame) retCtx = do
  case res of
    ROp dval@(DVal hName opName opExpr args oCtx) ctx' frame' dframe' knext -> do
      if hName == label then do
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
            env' <- rebindAll openv retCtx
            let newEnv = foldl (\acc x -> extendEnv acc (contextId op) x) env' params
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (\n -> fromJust $ lookupEnv n newEnv) params)
            if isTailOp opConName then do
              res <- eval opBod (limitEnv newEnv (fvs opBod))
              let kaddr = BindKImplicitAddr retCtx venv (contextId op)
              extendStore kaddr (AChangeKont knext venv h)
              doContinue res (FResume ctx' kaddr venv h (contextId opBod)) retCtx
            else if isNeverOp opConName then do
              returnV $ eval opBod (limitEnv newEnv (fvs opBod))
            else do
              extendStore (BindingAddr retCtx (last params) (contextId op)) (AChangeKont knext venv h)
              returnV $ eval opBod (limitEnv newEnv (fvs opBod))
      else do
        -- trace ("Allocating new return\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n" ++ show label ++ "," ++ show opName ++ "\n") $ return ()
        let k' = KAddr frame' ctx' dframe' dval
        let dframe = DFrame venv bodId h
        extendKStore k' (FRestoreDelim dframe) knext
        returnOp dval (static retCtx) (FRestoreDelim dframe) k'
    res ->
      case mbFrame of
        Just frame -> do
          -- trace ("Continuing after handling effects\n" ++ show retCtx ++ "\n") $ return ()
          doContinue res frame retCtx
        Nothing -> return $ RV res

branchMatch :: HasCallStack => ExprContext -> Branch -> AChangeTree -> VEnv -> CombinedCtx -> FixAAMR r s e (Either AChangeTree (Bindings r s e) )
branchMatch branchCtx branch addr env ctx = do
  match <- patMatch (head $ branchPatterns branch) addr
  case match of
    Left tree -> return $ Left tree
    Right (bindings, tree) ->
      if isExprTrue (guardTest $ head (branchGuards branch)) then return $ Right (bindings, tree)
      else do
        guard <- focusGuardExpr branchCtx
        let newEnv = foldl (\acc tname -> extendEnv acc (contextId branchCtx) tname) env (M.keys bindings)
        mapM_ (\(tname, extend) ->
          extend (fromJust $ lookupEnv tname newEnv)
          ) (M.toList bindings)
        RVAddr a <- eval guard newEnv
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
  deriving Show

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

-- rebind goes through memoization boundary (calls store -> doStep).
-- No infinite loops: either addresses are equal (returns immediately) or
-- computation joins via lattice and terminates due to finite height.
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

-- Pattern matching recursion is bounded by the finite pattern structure from source program.
-- Each recursive call to patMatch processes a structurally smaller pattern (PatVar removes one layer).
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
patMatch (PatCon nm pats _ _ _ _ _ _) tree = do
  let newArgs args [] = map (TChangeV . snd) args -- take the rest as is
      newArgs (_:args) (n:rest) = n : newArgs args rest -- prefer known tree elements
  -- TODO: Early catch of wrong type
  v <- changeOfTree tree
  case v of
    AChangeObj name args ->
      if name == getName nm then do
        let patArgs = zip pats (newArgs args (argsOfChange tree))
        matches <- mapM (uncurry patMatch) patArgs
        let newTree = treeUnion tree $ TChangeCon (addrOfTree tree) v (M.fromList (zip (map fst args) (map getTree matches)))
        if all isRight matches then
          return $ Right (M.unions (map (\(Right match) -> fst match) matches), newTree)
        else return $ Left newTree
      else return $ Left tree
    AChangeConstr conName params ->
      if null pats && getName nm == conName then return (Right (M.empty, TChangePartialCon (addrOfTree tree) v))
      else return $ Left tree
    _ -> return $ Left tree