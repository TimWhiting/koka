{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use map with tuple-section" #-}
module Core.FlowAnalysis.Full.DMCFAR.DMCFA where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Full.DMCFAR.AbstractValue
import Core.FlowAnalysis.Full.DMCFAR.Monad
import Core.FlowAnalysis.Full.DMCFAR.Primitives
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
      VStore addr ->
        trace ("Value not found in store :" ++ show addr)
        doBottom
      KStore addr -> if addr == EndKAddr then return $ KV KEnd else doBottom
      Step (CEval expr ctx) -> doEval expr ctx
      Step (CApply kaddr addr ctx) -> doApply kaddr addr ctx
      Step (CContinue res frame ctx targetId) -> doContinue res frame ctx targetId
      Step (CHandleEffects res retCtx newctx bodId hnd) -> doHandleEffects res retCtx newctx bodId hnd
      Step (CHandleLocal res retCtx newctx bodId varName valAddr) -> doHandleLocal res retCtx newctx bodId varName valAddr

extendStore :: Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  -- case addr of
  --   BindImplicitAddr{} -> return ()
  --   ConImplicitAddr{} -> return ()
  --   _ -> trace ("Extending store: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (VStore addr) (SV v)
extendKStore :: Addr -> Kont -> FixAAMR r e s ()
extendKStore addr v = do
  -- trace ("Extending KStore: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (KStore addr) (KV v)

store addr = do
  SV res <- doStep (VStore addr)
  return res
kStore addr = do
  KV res <- doStep (KStore addr)
  return res
eval expr ctx = doStep $ Step (CEval expr ctx)
apply kaddr addr ctx = doStep $ Step (CApply kaddr addr ctx)
continue res frame ctx targetId = doStep $ Step (CContinue res frame ctx targetId)
handleEffects res retCtx newctx bodId hnd = doStep $ Step (CHandleEffects res retCtx newctx bodId hnd)
handleLocal res retCtx newctx bodId varName valAddr = doStep $ Step (CHandleLocal res retCtx newctx bodId varName valAddr)

allocConst :: CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst ctx expr v = do
  let addr = BindImplicitAddr ctx (contextId expr)
  extendStore addr v
  return addr

allocFrame :: HasCallStack => Frame -> Addr -> CombinedCtx -> ExprContextId -> FixAAMR r s e Addr
allocFrame frame kaddr ctx u = do
  let addr = ImplicitAddr ctx u
  extendKStore addr (KNext frame (static ctx) kaddr)
  return addr

fvsl :: [ExprContext] -> S.Set TName
fvsl exprs = S.unions $ map fvs exprs

doEval :: HasCallStack => ExprContext -> CombinedCtx -> FixAAMR r s e FixChange
doEval expr ctx = do
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
        App e _ _ -> isSimpleExpr e
        _ -> False
      process x = if not open && not (isSimpleExpr (exprOfCtx expr)) then do
                    -- analysisLog ("Evaluating: " ++ showCtxExpr expr ++ ":" ++ show ctx ++ " with env " ++ show venv)
                    x
                  else x-- trace ("Evaluating: " ++ show expr ++ " in " ++ show (M.toList venv) ++ " : " ++ show ctx) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
   in process $ case exprOfCtx expr of
    App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen || getName name == namePretendDecreasing -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      eval f ctx
    App (TypeApp (Var name _) _) [_,_,f] _ | getName name == nameMaskAt -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 3 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f ctx
      doContinue res FMask ctx (contextId f)
    App (TypeApp (Var name _) _) [f] _ | getName name == nameMaskBuiltin -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f ctx
      doContinue res FMask ctx (contextId f)
    Con tn _ _ -> do
      let params = case splitFunScheme (typeOf tn) of
                      Just (_, params, _, _) -> map fst params
                      Nothing -> []
      -- trace ("Con: " ++ show tn ++ " with params: " ++ show params) $ return ()
      let constr = AChangeConstr expr params
      RV . RVAddr <$> allocConst ctx expr constr
    Var name _ -> do
      if isPrimitive name && not (isTrickyPrimitive name) then do
        -- trace ("Primitive " ++ show name) $ return ()
        RV . RVAddr <$> allocConst ctx expr (AChangePrim name expr)
      else if qualifier (getName name) == nameCoreHnd then
        error ("Unexpected handler library name in DMCFA: " ++ show name)
      else if qualifier (getName name) == nameNil then do
        -- trace ("Found variable: " ++ show name ++ " at " ++ show name) $ return ()
        return $ RV $ RVAddr (BindingAddr ctx name)
      else do
        -- trace ("Evaluating external: " ++ show name) $ return ()
        res <- bindExternal (equalPrimitive name)
        case res of
          Just expr -> do
            c <- startCombinedCtx
            eval expr c
          Nothing -> trace ("Variable not found: " ++ show name) doBottom
    Lit l -> RV . RVAddr <$> allocConst ctx expr (injLit (contextId expr) l)
    Lam{} -> RV . RVAddr <$> allocConst ctx expr (AChangeClos expr ctx)
    App _ args _ -> doApp args
    Let dgs _ -> do
      child <- childrenContexts expr
      -- trace ("LetChildren: " ++ intercalate "\n" (map show child)) $ return ()
      bind <- focusLetDefBinding 0 0 expr
      let defGroup = head dgs
      -- let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) (defsOf defGroup)
      let defName = defTName (defOfCtx bind)
      -- trace ("Let binding: " ++ show defName ++ " in " ++ show newEnv) $ return ()
      res <- eval bind ctx
      doContinue res (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr) ctx (contextId bind)
    TypeApp{} -> do
      e <- focusChild 0 expr
      eval e ctx
    TypeLam _ Lam{} -> RV . RVAddr <$> allocConst ctx expr (AChangeClos expr ctx)
    TypeLam _ (App _ args _) -> doApp args
    TypeLam _ _ -> do --(TypeApp Var{} _)
      childs <- childrenContexts expr
      -- trace ("TypeLam: " ++ show (map contextId childs)) $ return ()
      e <- focusChild 0 expr
      eval e ctx
    Case _ brs -> do
      s <- focusScrutinee expr
      branches <- mapM (\i -> focusBranch i expr) [0..length brs - 1]
      res <- eval s ctx
      doContinue res (FScrut expr branches) ctx (contextId s)
    -- TypeLam _ e -> do
    --   trace ("TypeLam not handled yet: " ++ show e) $ doBottom
  where doApp args = do
          f <- focusFun expr
          argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
          -- trace ("Applying function: " ++ show f ++ " to args: " ++ show argExprs ++ " with env " ++ show venv) $ return ()
          res <- eval f ctx
          doContinue res (FApp (length args) argExprs [] expr) ctx (contextId f)


doContinue :: HasCallStack => FixChange -> Frame -> CombinedCtx -> ExprContextId -> FixAAMR r s e FixChange
doContinue res frame ctx targetId =
  -- trace ("Continuing: with frame " ++ show frame ++ " in " ++ show ctx) $
  case res of
    RV (ROp knext dval) -> do
      k' <- allocFrame frame knext ctx targetId
      return $ RV $ ROp k' dval
    RV (RVAddr addr) -> do
      case frame of
          f | f == FCall || f == FMask -> do
            v <- store addr
            case v of
              AChangeClos e env -> do
                bod <- focusBody e
                eval bod ctx
          FApp n args res eApp -> do
            let uApp = contextId eApp
            case args of
              [] -> case res ++ [addr] of
                f:arguments -> do
                  -- trace ("Applying: " ++ show args ++ " " ++ show (res ++ [addr])) $ return ()
                  -- trace ("Real params: " ++ show params) $ return ()
                  res <- store f
                  -- trace ("Applying function: " ++ show f ++ " " ++ show res) $ return ()
                  case res of
                    AChangeClos cexpr cenv -> do
                      body <- focusBody cexpr
                      let args = lamNames cexpr
                      m <- mLimit
                      let newCtx = addCall m ctx uApp
                      -- let newEnv = foldl (\acc x -> M.insert x newCtx acc) args
                      -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show args) $ return ()
                      zipWithM_ (\a p -> rebind p (BindingAddr newCtx a)) args arguments
                      eval body newCtx
                    AChangePrim name pms -> do
                      let addr = BindImplicitAddr ctx uApp
                      let n = getName name
                      if not (isHandlerPrimitive n) then do
                        args <- mapM store arguments
                        res <- doPrimitive n args
                        extendStore addr res
                        return $ RV $ RVAddr addr
                      else doHandlerPrimitive name n addr arguments ctx eApp
                    AChangeConstr con params -> do
                      let name = case exprOfCtx con of
                            Con n _ _ -> n
                            _ -> error "Expected a constructor"
                      let addr = BindImplicitAddr ctx uApp
                      let conParams = map (\nm -> ConImplicitAddr nm ctx uApp) params
                      zipWithM_ rebind arguments conParams
                      extendStore addr (AChangeObj con name (zip params conParams))
                      -- extendStore addr (AChangeObj con name (zip params arguments))
                      return $ RV $ RVAddr addr
                    AChangeKont label kx hctx hnd -> do
                      m <- mLimit
                      d <- dLimit
                      let newCtx = addCall m ctx uApp
                          newDynCtx = addDelim d newCtx uApp label
                      -- trace ("Applying continuation\n" ++ show uApp ++ "\n" ++ show newCtx ++ "\n" ++ show newDynCtx) $ return () -- ++ "for\n" ++
                      res <- doApply kx addr newDynCtx
                      handleEffects res newCtx (CombinedCtx (TKDelim startDelimCtx) newDynCtx) uApp hnd
                    _ -> do
                      trace ("Applying non function: " ++ show res) doBottom
              next:rest -> do
                -- trace ("Next " ++ show next) $ return ()
                ret <- eval next ctx
                continue ret (FApp n rest (res ++ [addr]) eApp) ctx (contextId next)
          FLet groupIdx numGroups bindingIdx numBindings name resolved u -> do
            -- trace ("Applying Let " ++ show newctx ++ " env " ++ show venv) $ return ()
             -- We need to override the old name binding (in case it was in a different context)
            rebind addr (BindingAddr ctx name)
            -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show venv ) $ return ()
            -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
            if isLetDefBindingFinished groupIdx bindingIdx u then do
              -- trace ("Let group finished: " ++ show groupIdx ++ " of " ++ show numGroups) $ return ()
              body <- focusLetBod u
              eval body ctx
            else do
              -- trace ("Let group next: " ++ show groupIdx ++ ", " ++ show bindingIdx) $ return ()
              next <- focusNextLetDefBinding groupIdx bindingIdx u
              ret <- eval next ctx
              continue ret (nextLetFrame frame ctx) ctx (contextId next)
          FScrut parent branches -> do
            let recur [] = doBottom
                recur ((branch, expr):branches) = do
                  match <- branchMatch branch addr
                  case match of
                    Just bindings -> do                      
                      mapM_ (\(tname, extend) ->
                        extend (BindingAddr ctx tname)
                        ) (M.toList bindings)
                      eval expr ctx
                    Nothing -> recur branches
            case exprOfCtx parent of
              Case _ pats -> recur (zip pats branches)
          FDollar va -> do
            res <- store va
            case res of
              AChangeClos cexpr cenv -> do
                  body <- focusBody cexpr
                  let [arg] = lamNames cexpr
                  m <- mLimit
                  -- let newEnv = M.insert arg ctx cenv
                  rebind addr (BindingAddr ctx arg)
                  eval body ctx
          FResume kont hnd u -> do
            m <- mLimit
            d <- dLimit
            let newRetCtx = addCall m ctx u
                newDelimCtx = addDelim d newRetCtx u (hLabel hnd)
            -- trace ("Applying continuation " ++ show (contextId u) ++ " " ++ show henv ) $ return () -- ++ "for\n" ++ 
            apply kont addr newDelimCtx 
            handleEffects res newRetCtx (CombinedCtx (TKDelim startDelimCtx) newDelimCtx) u hnd
          _ -> do
            error ("Continuing: " ++ show res ++ " with unknown frame " ++ show frame)

doApply :: HasCallStack => Addr -> Addr -> DynamicCtx -> FixAAMR r s e FixChange
doApply kaddr addr dynctx = do
  -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show dynctx) $ return ()
  k <- kStore kaddr
  -- trace ("Applying: " ++ show k) $ return ()
  case k of
    KEnd -> return $ RV $ RVAddr addr
    KNext frame ctx knext -> do
      res <- apply knext addr dynctx
      let newctx = CombinedCtx ctx dynctx
      doContinue res frame newctx (kaddrId kaddr)
    KLocal knext bodyId varName varAddr ctx dCtx -> do
      let newctx = CombinedCtx ctx dynctx
      d <- dLimit
      m <- mLimit 
      let newRetCtx = addCall m newctx bodyId
      let (id, nm) = ctxHnd dCtx
      let newDelimCtx = newDelim d m newRetCtx id nm
      res <- apply knext addr (dynamic newDelimCtx)
      handleLocal res newRetCtx newDelimCtx bodyId varName varAddr
    KLink knext retCtx dCtx bodId h -> do -- TODO: Dynamic context adjustments...
      let newctx = CombinedCtx (static retCtx) dynctx
      d <- dLimit
      m <- mLimit 
      let newRetCtx = addCall m newctx bodId
      let (id, nm) = ctxHnd dCtx
      let newDelimCtx = newDelim d m newRetCtx id nm
      res <- apply knext addr (dynamic newDelimCtx)
      -- trace ("Restoring handler context for " ++ show h ++ " with\n" ++ show newRetCtx ++ "\n" ++ show newDelimCtx ++ "\n") $ return () 
      handleEffects res newRetCtx newDelimCtx bodId h
isHandlerPrimitive :: Name -> Bool
isHandlerPrimitive n =
  n == nameHandle || isClauseName n || n == nameHTag
  || n == nameEvvAt || n == nameMaskAt || isNamePerform n || isClauseName n
  || n == nameLocalVar || n == nameLocalGet || n == nameLocalSet

doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> [Addr] -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
doHandlerPrimitive name n addr arguments ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
  extendStore addr (AChangeObj u name (zip (repeat nameNil) arguments))
  return $ RV $ RVAddr addr
doHandlerPrimitive name n addr arguments ctx u | isNamePerform n = do
  args <- mapM store arguments
  let label = case exprOfCtx u of
        App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 1))
        _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
  let AChangeClos select senv = args !! 1
  let DefCNonRec _ _ opName = select
  let opN = newName $ nameLocalQual (getName opName)
  -- trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
  return $ RV $ ROp EndKAddr $ DVal label opN u (drop 2 arguments) ctx
doHandlerPrimitive name n addr arguments ctx u | n == nameLocalGet = do
  -- trace ("LocalGet: " ++ show name ++ " " ++ show n ++ "\n" ++ show (head arguments)) $ return ()
  if localEff then do
    let [varAddr@(BindingAddr _ varName), _] = arguments
    return $ RV $ ROp EndKAddr $ DVal (getName varName) nameLocalGet u (drop 2 arguments) ctx
  else do
    return $ RV $ RVAddr (head arguments)
doHandlerPrimitive name n addr arguments ctx u | n == nameLocalSet = do
  let [varAddr@(BindingAddr _ varName), val] = arguments
  -- trace ("LocalSet: " ++ show name ++ " " ++ show n ++ "\n" ++ show args ++ "\n" ++ show arguments) $ return ()
  if localEff then do
    return $ RV $ ROp EndKAddr $ DVal (getName varName) nameLocalSet u [val] ctx
  else do
    rebind val varAddr
    extendStore addr changeUnit
    return $ RV $ RVAddr addr
doHandlerPrimitive name n addr arguments ctx u | n == nameHandle = do
  args <- mapM store arguments
  case args of
    [AChangeObj _ _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] -> do
      let label = case exprOfCtx u of
            App (TypeApp _ [_, _, _, h, _]) _ _ -> labelName h
      d <- dLimit
      m <- mLimit
      -- trace ("OPS " ++ show henv) $ return ()
      bod <- focusBody body
      let newctx = newDelim d m ctx (contextId u) label
      res <- eval bod newctx
      let h = Handler label (arguments !! 1) (Just ret) (Just $ FDollar (arguments !! 2))
      handleEffects res ctx newctx (contextId bod) h
    _ -> doBottom
doHandlerPrimitive name n addr arguments ctx u | n == nameLocalVar = do
  args <- mapM store arguments
  -- trace ("LocalVar: " ++ show name ++ " " ++ show n) $ return ()
  if localEff then do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        -- let newEnv = M.insert varName ctx env
        bod <- focusBody e
        d <- dLimit
        m <- mLimit
        let newctx = newDelim d m ctx (contextId u) (getName varName)
        res <- eval bod newctx
        handleLocal res ctx newctx (contextId bod) (getName varName) (head arguments)
  else do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        -- let newEnv = M.insert varName ctx env
        bod <- focusBody e
        rebind (head arguments) (BindingAddr ctx varName)
        eval bod ctx
localEff = True

doHandleLocal :: HasCallStack => FixChange -> CombinedCtx -> CombinedCtx -> ExprContextId -> Name -> Addr -> FixAAMR r s e FixChange
doHandleLocal res retCtx newctx bodId varName valAddr = do
  case res of
    RV (ROp knext dval) -> do
      case dval of
        DVal hName opName oExpr args oCtx | hName == varName && opName == nameLocalGet -> do
          res <- apply knext valAddr (dynamic retCtx)
          handleLocal res retCtx newctx bodId varName valAddr
        DVal hName opName oExpr [newAddr] oCtx | hName == varName && opName == nameLocalSet -> do
          let addr = ImplicitAddr retCtx (contextId oExpr)
          extendStore addr changeUnit
          res <- apply knext addr (dynamic retCtx)
          handleLocal res retCtx newctx bodId varName newAddr
        DVal hName opName opExpr args oCtx -> do
          trace ("Passing along local operation: " ++ show opName ++ " at local " ++ show varName ++ " searching for " ++ show hName) $ return ()
          let k' = ImplicitLAddr retCtx newctx varName opName (contextId opExpr)
          extendKStore k' (KLocal knext bodId varName valAddr (static newctx) newctx)
          return $ RV $ ROp k' dval
    RV (RVAddr addr) -> return $ RV $ RVAddr addr

doHandleEffects :: HasCallStack => FixChange -> CombinedCtx -> CombinedCtx -> ExprContextId -> Handler -> FixAAMR r s e FixChange
doHandleEffects res retCtx delimCtx bodId h@(Handler label hnd mbRet mbFrame) = do
  case res of
    RV (ROp kOp (DVal hName opName opExpr args oCtx)) -> do
      if hName == label then do
        -- trace ("Evaluating operation: " ++ show opName ++ " at handler " ++ show label) $ return ()
        AChangeObj _ tname hndargs@(_:ops) <- store hnd
        let ops' = map (\(n, a) -> (unmakeOpHidden opName $ nameStem n, a)) ops
        case lookup opName ops' of
          Nothing -> error ("Unwind: Operation " ++ show opName ++ " not found in " ++ show ops')
          Just op -> do
            o <- store op
            -- trace ("Unwinding operation: " ++ show opName ++ " with " ++ show o) $ return ()
            AChangeObj _ opConName [opAddr] <- store op
            AChangeClos op openv <- store (snd opAddr)
            let params = lamNames op
            opBod <- focusBody op
            -- let newEnv = foldl (\acc x -> M.insert x retCtx acc) openv params
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (BindingAddr retCtx) params)
            if isTailOpT opConName then do -- TODO: TIM
              res <- eval opBod retCtx
              case res of -- Extract as continueApply?
                RV (RVAddr addr) -> do
                  res <- apply kOp addr (dynamic retCtx)
                  d <- dLimit
                  m <- mLimit
                  let newRetCtx = addCall m retCtx (contextId opBod)
                  let newDelimCtx = newDelim d m newRetCtx (contextId opBod) label
                  handleEffects res newRetCtx newDelimCtx bodId h
                RV (ROp knext dval) -> do
                  k' <- allocFrame (FResume kOp h (contextId opBod)) knext retCtx (contextId opBod)
                  return $ RV $ ROp k' dval
            else if isNeverOp opConName then do
              eval opBod retCtx
            else do
              extendStore (BindingAddr retCtx (last params)) (AChangeKont hName kOp retCtx h)
              eval opBod retCtx
      else do
        -- trace ("Allocating new return\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n" ++ show label ++ "," ++ show opName ++ "\n") $ return ()
        let k' = ImplicitLAddr retCtx delimCtx label opName (contextId opExpr)
        extendKStore k' (KLink kOp retCtx delimCtx bodId h)
        return $ RV (ROp k' (DVal hName opName opExpr args oCtx))
    res ->
      case mbFrame of
        Just frame -> do
          -- trace ("Continuing after handling effects\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n") $ return ()
          continue res frame retCtx bodId
        Nothing -> return res

branchMatch :: Branch -> Addr -> FixAAMR r s e (Maybe (Bindings r s e))
branchMatch branch addr =
  patMatch (head $ branchPatterns branch) addr

type Bindings r s e = M.Map TName (Addr -> FixAAMR r s e ())

rebind :: Addr -> Addr -> FixAAMR r s e ()
rebind oldAddr newAddr = do
  each [do
          rebind oldAddr newAddr
          doBottom ,
        return ()]

patMatch :: Pattern -> Addr -> FixAAMR r s e (Maybe (Bindings r s e))
patMatch (PatVar name rest) addr = do
  match <- patMatch rest addr
  case match of
    Just bindings -> return $ Just $ M.insert name (\newAddr -> rebind addr newAddr) bindings
    Nothing -> return Nothing
patMatch PatWild addr = return $ Just M.empty
patMatch plit@(PatLit _) addr = do
  v <- store addr
  case v of
    AChangeLit litChange ->
      if patSubsumedX plit litChange then return $ Just M.empty
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
          return $ Just $ M.unions (map fromJust matches)
        else return Nothing
      else return Nothing
    AChangeConstr con params ->
      case exprOfCtx con of
        Con conName _ _ ->
         if null pats && nm == conName then return (Just M.empty)
         else return Nothing
    _ -> return Nothing