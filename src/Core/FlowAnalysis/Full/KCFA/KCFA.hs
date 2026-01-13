{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use map with tuple-section" #-}
module Core.FlowAnalysis.Full.KCFA.KCFA where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Full.KCFA.AbstractValue
import Core.FlowAnalysis.Full.KCFA.Monad
import Core.FlowAnalysis.Full.KCFA.Primitives
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
import Data.Either (isRight)

doStep :: HasCallStack => FixInput -> FixAAMR r s e FixChange
doStep i =
  memo i $ do
    case i of
      VStore addr ->
        trace ("Value not found in store :" ++ show addr)
        doBottom
      KStore addr -> if addr == EndKAddr then return $ KV EndKAddr else doBottom
      Step (CEval expr venv ctx) -> doEval expr venv ctx
      Step (CApply kaddr addr ctx) -> doApply kaddr addr ctx
      Step (CHandleEffects res venv bodId hnd ctx) -> doHandleEffects res venv bodId hnd ctx
      Step (CHandleLocal res venv bodId varName valAddr retCtx) -> doHandleLocal res venv bodId varName valAddr retCtx

extendStore :: Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  -- case addr of
  --   BindImplicitAddr{} -> return ()
  --   ConImplicitAddr{} -> return ()
    -- _ -> trace ("Extending store: " ++ show addr ++ " with " ++ show v) $ return ()
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
eval expr venv ctx = doStep $ Step (CEval expr venv ctx)
apply kaddr addr ctx = doStep $ Step (CApply kaddr addr ctx)
handleEffects res venv bodId hnd retCtx = doStep $ Step (CHandleEffects res venv bodId hnd retCtx)
handleLocal res venv bodId varName valAddr retCtx = doStep $ Step (CHandleLocal res venv bodId varName valAddr retCtx)

returnConst :: VEnv -> StaticCtx -> ExprContext -> AChange -> FixAAMR r s e FixChange
returnConst env ctx expr v = do 
  addr <- allocConst env ctx expr v
  return $ RV (RVAddr addr, ctx)

returnOp :: DelimitedVal -> StaticCtx -> Frame ->  DelimitedFrame -> Addr -> FixAAMR r s e FixChange
returnOp dval ctx frame dframe kaddr = return $ RV $ (ROp dval ctx frame dframe kaddr, ctx)

returnAddr :: Addr -> StaticCtx -> FixAAMR r s e FixChange
returnAddr addr ctx = return $ RV (RVAddr addr, ctx)


allocConst :: VEnv -> StaticCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst env ctx expr v = do
  let addr = BindImplicitAddr ctx (limitEnv env (fvs expr)) (contextId expr)
  extendStore addr v
  return addr

fvsl :: [ExprContext] -> S.Set TName
fvsl exprs = S.unions $ map fvs exprs

doEval :: HasCallStack => ExprContext -> VEnv -> StaticCtx -> FixAAMR r s e FixChange
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
      eval f venv ctx
    App (TypeApp (Var name _) _) [_,_,f] _ | getName name == nameMaskAt -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 3 expr
      -- trace ("Masking " ++ show f) $ return ()
      RV (res, newCtx) <- eval f venv ctx
      doContinue res FMask newCtx
    App (TypeApp (Var name _) _) [f] _ | getName name == nameMaskBuiltin -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      -- trace ("Masking " ++ show f) $ return ()
      RV (res, newCtx) <- eval f venv ctx
      doContinue res FMask newCtx
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
        Just addr -> returnAddr addr ctx
        Nothing -> do
          -- trace ("Evaluating external: " ++ show name) $ return ()
          res <- bindExternal (equalPrimitive name)
          case res of
            Just expr -> do
              RV (res, ctx_) <- eval expr M.empty startStaticCtx
              return $ RV (res, ctx)
            Nothing -> trace ("Variable not found: " ++ show name) doBottom
    Lit l -> returnConst venv ctx expr (injLit (contextId expr) l)
    Lam{} -> returnConst venv ctx expr (AChangeClos expr venv)
    App _ args _ -> doApp args
    Let dgs _ -> doLet dgs
    TypeApp{} -> do
      e <- focusChild 0 expr
      eval e venv ctx
    TypeLam _ Lam{} -> returnConst venv ctx expr (AChangeClos expr venv)
    TypeLam _ (App _ args _) -> doApp args
    TypeLam _ (Let dgs _) -> doLet dgs
    TypeLam _ _ -> do --(TypeApp Var{} _)
      childs <- childrenContexts expr
      -- trace ("TypeLam: " ++ show (map contextId childs)) $ return ()
      e <- focusChild 0 expr
      eval e venv ctx
    Case _ brs -> do
      s <- focusScrutinee expr
      branches <- mapM (\i -> focusBranch i expr) [0..length brs - 1]
      RV (res, newCtx) <- eval s (limitEnv venv (fvs s)) ctx
      doContinue res (FScrut expr branches venv) newCtx
    -- TypeLam _ e -> do
    --   trace ("TypeLam not handled yet: " ++ show e) $ doBottom
  where 
    doLet dgs = do 
          child <- childrenContexts expr
          -- trace ("LetChildren: " ++ intercalate "\n" (map show child)) $ return ()
          bind <- focusLetDefBinding 0 0 expr
          let defGroup = head dgs
          let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
          let defName = defTName (defOfCtx bind)
          -- trace ("Let binding: " ++ show defName ++ " in " ++ show newEnv) $ return ()
          RV (res, newCtx) <- eval bind (limitEnv newEnv (S.insert defName (fvs bind))) ctx
          doContinue res (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr newEnv) newCtx 
    doApp args = do
          f <- focusFun expr
          argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
          -- trace ("Applying function: " ++ show f ++ " to args: " ++ show argExprs ++ " with env " ++ show venv) $ return ()
          RV (res, newCtx) <- eval f (limitEnv venv (fvs f)) ctx
          doContinue res (FApp (length args) argExprs [] expr venv) newCtx

doContinue :: HasCallStack => RValue -> Frame -> StaticCtx -> FixAAMR r s e FixChange
doContinue res frame ctx =
  case res of
    ROp dval ctx' frame' dframe knext -> do
      let k' = KAddr frame' ctx' dframe dval
      extendKStore k' knext
      returnOp dval ctx frame dframe k'
    RVAddr addr -> do
      -- trace ("Continuing: with frame " ++ show frame ++ " in " ++ show ctx) $ return ()
      case frame of
          FrameDone -> returnAddr addr ctx
          f | f == FMask -> do
            v <- store addr
            case v of
              AChangeClos e env -> do
                bod <- focusBody e
                eval bod env ctx
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
                      eval body (limitEnv newEnv (fvs body)) newCtx
                    AChangePrim name pms -> do
                      let retAddr = BindImplicitAddr ctx venv uApp
                      let n = getName name
                      if not (isHandlerPrimitive n) then do
                        args <- mapM store arguments
                        res <- doPrimitive n args store
                        extendStore retAddr res
                        returnAddr retAddr ctx
                      else doHandlerPrimitive name n retAddr arguments venv ctx eApp
                    AChangeConstr con params -> do
                      let name = case exprOfCtx con of
                            Con n _ _ -> n
                            _ -> error "Expected a constructor"
                      let retAddr = BindImplicitAddr ctx venv uApp
                      let conParams = map (\nm -> ConImplicitAddr nm ctx uApp) params
                      zipWithM_ rebind arguments conParams
                      extendStore retAddr (AChangeObj con name (zip params conParams))
                      -- extendStore retAddr (AChangeObj con name (zip params arguments))
                      returnAddr retAddr ctx
                    AChangeKont kx henv hnd -> do
                      m <- mLimit
                      let newCtx = addCall m ctx uApp
                      -- trace ("Applying continuation\n" ++ show uApp ++ "\n" ++ show newCtx) $ return () -- ++ "for\n" ++
                      RV (res, newCtx') <- apply kx addr newCtx
                      handleEffects res henv uApp hnd newCtx'
                    _ -> do
                      trace ("Applying non function: " ++ show res) doBottom
              next:rest -> do
                -- trace ("Next " ++ show next) $ return ()
                RV (ret, newCtx) <- eval next (limitEnv venv (fvs next)) ctx
                doContinue ret (FApp n rest (res ++ [addr]) eApp venv) newCtx
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
              eval body (limitEnv env' (fvs body)) ctx
            else do
              -- trace ("Let group next: " ++ show groupIdx ++ ", " ++ show bindingIdx) $ return ()
              next <- focusNextLetDefBinding groupIdx bindingIdx u
              RV (ret, newCtx) <- eval next env' ctx
              doContinue ret (nextLetFrame frame newCtx) newCtx
          FScrut parent branches env -> do
            let recur [] tree = doBottom
                recur ((branch, br):branches) tree = do
                  match <- branchMatch br branch tree env ctx
                  case match of
                    Right (bindings, matchTree) -> do
                      let newEnv = foldl (\acc tname -> M.insert tname ctx acc) env (M.keys bindings)
                      mapM_ (\(tname, extend) ->
                        extend (fromJust $ lookupEnv tname newEnv)
                        ) (M.toList bindings)
                      each [
                          do
                            body <- focusBranchExpr br
                            eval body (limitEnv newEnv (fvs body)) ctx,
                          if definitelyMatched matchTree then doBottom
                          else recur branches matchTree
                       ]
                    Left newTree -> recur branches newTree
            case exprOfCtx parent of
              Case _ pats -> recur (zip pats branches) (TChangeV addr)
          FDollar va -> do
            res <- store va
            case res of
              AChangeClos cexpr cenv -> do
                  body <- focusBody cexpr
                  let [arg] = lamNames cexpr
                  m <- mLimit
                  let newCtx = addCall m ctx (contextId cexpr)
                  let newEnv = M.insert arg newCtx cenv
                  v <- store addr
                  extendStore (fromJust $ lookupEnv arg newEnv) v
                  eval body (limitEnv newEnv (fvs body)) newCtx
              _ -> doBottom
          FResume kont venv hnd u -> do
            m <- mLimit
            let newRetCtx = addCall m ctx u
            -- trace ("Applying continuation " ++ show (contextId u) ++ " " ++ show henv ) $ return () -- ++ "for\n" ++ 
            RV (res, newCtx) <- apply kont addr newRetCtx 
            handleEffects res venv u hnd newCtx
          _ -> do
            error ("Continuing: " ++ show res ++ " with unknown frame " ++ show frame)

doApply :: HasCallStack => Addr -> Addr -> StaticCtx -> FixAAMR r s e FixChange
doApply kaddr addr ctx = do
  -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show dynctx) $ return ()
  -- trace ("Applying: " ++ show k) $ return ()
  case kaddr of
    EndKAddr -> returnAddr addr ctx
    KAddr (FRestoreDelim (DFrameLocal venv bodId varName varAddr)) _ _ _ -> do
      knext <- kStore kaddr
      RV (res, newctx) <- apply knext addr ctx
      handleLocal res venv bodId varName varAddr newctx
    KAddr (FRestoreDelim (DFrame venv bodId h)) _ _ _ -> do
      knext <- kStore kaddr
      RV (res, newctx) <- apply knext addr ctx
      -- trace ("Restoring handler context for " ++ show h ++ " with\n" ++ show newRetCtx ++ "\n" ++ show newDelimCtx ++ "\n") $ return () 
      handleEffects res venv bodId h newctx
    KAddr frame _ _ _ -> do
      knext <- kStore kaddr
      RV (res, newctx) <- apply knext addr ctx
      doContinue res frame newctx

isHandlerPrimitive :: Name -> Bool
isHandlerPrimitive n =
  n == nameHandle || isClauseName n || n == nameHTag
  || n == nameEvvAt || n == nameMaskAt || isNamePerform n || isClauseName n
  || n == nameLocalVar || n == nameLocalGet || n == nameLocalSet

doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> [Addr] -> VEnv -> StaticCtx -> ExprContext -> FixAAMR r s e FixChange
doHandlerPrimitive name n addr arguments venv ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
  extendStore addr (AChangeObj u name (zip (repeat nameNil) arguments))
  returnAddr addr ctx
doHandlerPrimitive name n addr arguments venv ctx u | isNamePerform n = do
  let label = case exprOfCtx u of
        App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 1))
        _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
  AChangeClos select senv <- store (arguments !! 1)
  let DefCNonRec _ _ opName = select
  let opN = newName $ nameLocalQual (getName opName)
  m <- mLimit
  -- trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
  returnOp (DVal label opN u (drop 2 arguments)) ctx FrameDone DFrameDone EndKAddr
doHandlerPrimitive name n addr arguments venv ctx u | n == nameLocalGet = do
  -- trace ("LocalGet: " ++ show name ++ " " ++ show n ++ "\n" ++ show (head arguments)) $ return ()
  if localEff then do
    let [varAddr@(BindingAddr _ varName), _] = arguments
    returnOp (DVal (getName varName) nameLocalGet u []) ctx FrameDone DFrameDone EndKAddr
  else do
    returnAddr (head arguments) ctx
doHandlerPrimitive name n addr arguments venv ctx u | n == nameLocalSet = do
  let [varAddr@(BindingAddr _ varName), val] = arguments
  -- trace ("LocalSet: " ++ show name ++ " " ++ show n ++ "\n" ++ show args ++ "\n" ++ show arguments) $ return ()
  if localEff then do
    returnOp (DVal (getName varName) nameLocalSet u [val]) ctx FrameDone DFrameDone EndKAddr
  else do
    rebind val varAddr
    extendStore addr changeUnit
    returnAddr addr ctx
doHandlerPrimitive name n addr arguments venv ctx u | n == nameHandle = do
  args <- mapM store arguments
  case args of
    [AChangeObj _ _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] -> do
      let label = case exprOfCtx u of
            App (TypeApp _ [_, _, _, h, _]) _ _ -> labelName h
      m <- mLimit
      -- trace ("OPS " ++ show henv) $ return ()
      bod <- focusBody body
      -- trace ("Applying handle: " ++ show label ++ " with env " ++ show venv) $ return ()
      RV (res, newCtx) <- eval bod (limitEnv bodyenv (fvs body)) ctx
      let h = Handler label (arguments !! 1) (Just ret) (Just $ FDollar (arguments !! 2))
      handleEffects res venv (contextId bod) h newCtx
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
        RV (res, newCtx) <- eval bod newEnv ctx
        handleLocal res venv (contextId bod) varName (head arguments) newCtx
  else do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        let newEnv = M.insert varName ctx env
        bod <- focusBody e
        extendStore (fromJust $ lookupEnv varName newEnv) (head args)
        eval bod newEnv ctx
localEff = True

doHandleLocal :: HasCallStack => RValue -> VEnv -> ExprContextId -> TName -> Addr -> StaticCtx -> FixAAMR r s e FixChange
doHandleLocal res venv bodId varName valAddr ctx = do
  case res of
    ROp dval ctx' frame' dframe' knext -> do
      let kOp = KAddr frame' ctx' dframe' dval
      extendKStore kOp knext
      case dval of
        DVal hName opName oExpr args | hName == getName varName && opName == nameLocalGet -> do
          RV (res, newCtx) <- apply kOp valAddr ctx
          handleLocal res venv bodId varName valAddr newCtx
        DVal hName opName oExpr [newAddr] | hName == getName varName && opName == nameLocalSet -> do
          extendStore UnitAddr changeUnit
          m <- mLimit
          let xctx = addCall m ctx (contextId oExpr)
          RV (res, newCtx) <- apply kOp newAddr xctx
          handleLocal res venv bodId varName newAddr newCtx
        DVal hName opName opExpr args -> do
          -- trace ("Passing along local operation: " ++ show opName ++ " at local " ++ show varName ++ " searching for " ++ show hName) $ return ()
          let dframe = DFrameLocal venv bodId varName valAddr
          returnOp dval ctx (FRestoreDelim dframe) dframe kOp
    RVAddr addr -> returnAddr addr ctx

doHandleEffects :: HasCallStack => RValue -> VEnv -> ExprContextId -> Handler -> StaticCtx -> FixAAMR r s e FixChange
doHandleEffects res venv bodId h@(Handler label hnd mbRet mbFrame) ctx = do
  case res of
    ROp dval@(DVal hName opName opExpr args) ctx' frame' dframe' knext  -> do
      if hName == label then do
        let kOp = KAddr frame' ctx' dframe' dval
        extendKStore kOp knext
        -- trace ("Evaluating operation: " ++ show opName ++ " at handler " ++ show label) $ return ()
        AChangeObj _ tname hndargs@(_:ops) <- store hnd
        let ops' = map (\(n, a) -> (unmakeOpHidden opName $ nameStem n, a)) ops
        case lookup opName ops' of
          Nothing -> doBottom -- error ("Unwind: Operation " ++ show opName ++ " not found in " ++ show ops')
          Just op -> do
            AChangeObj _ opConName [opAddr] <- store op
            AChangeClos op openv <- store (snd opAddr)
            let params = lamNames op
            opBod <- focusBody op
            m <- mLimit
            let newCtx = addCall m ctx (contextId opBod)
            let newEnv = foldl (\acc x -> M.insert x newCtx acc) openv params
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (BindingAddr newCtx) params)
            if isTailOpT opConName then do -- TODO: Add operation call context?
              RV (res', retCtx') <- eval opBod (limitEnv newEnv (fvs opBod)) newCtx
              doContinue res' (FResume kOp venv h (contextId opBod)) retCtx'
            else if isNeverOp opConName then do
              eval opBod (limitEnv newEnv (fvs opBod)) newCtx
            else do
              extendStore (BindingAddr newCtx (last params)) (AChangeKont kOp venv h)
              eval opBod (limitEnv newEnv (fvs opBod)) newCtx
      else do
        -- trace ("Allocating new return\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n" ++ show label ++ "," ++ show opName ++ "\n") $ return ()
        let k' = KAddr frame' ctx' dframe' dval
        extendKStore k' knext
        let dframe = DFrame venv bodId h
        returnOp dval ctx (FRestoreDelim dframe) dframe k'
    res ->
      case mbFrame of
        Just frame -> do
          -- trace ("Continuing after handling effects\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n") $ return ()
          doContinue res frame ctx
        Nothing -> return $ RV (res, ctx)

branchMatch :: ExprContext -> Branch -> AChangeTree -> VEnv -> StaticCtx -> FixAAMR r s e (Either AChangeTree (Bindings r s e))
branchMatch branchCtx branch addr env ctx = do
  match <- patMatch (head $ branchPatterns branch) addr
  case match of 
    Left tree -> return $ Left tree
    Right (bindings, tree) -> 
      if isExprTrue (guardTest $ head (branchGuards branch)) then return $ Right (bindings, tree)
      else do
        let newEnv = foldl (\acc tname -> M.insert tname ctx acc) env (M.keys bindings)
        mapM_ (\(tname, extend) ->
          extend (fromJust $ lookupEnv tname newEnv)
          ) (M.toList bindings)
        guard <- focusGuardExpr branchCtx
        RV (RVAddr a, ctx') <- eval guard newEnv ctx -- TODO: Pass back the ctx'
        v <- store a
        case v of 
          AChangeConstr con _ -> 
            case exprOfCtx con of
              Con conName _ _ | getName conName == nameTrue ->
                return $ Right (bindings, tree)  
              _ -> return $ Left tree
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

rebind :: Addr -> Addr -> FixAAMR r s e ()
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
patMatch (PatCon nm pats _ _ _ _ _ _) tree = do
  let newArgs args [] = map (TChangeV . snd) args -- take the rest as is
      newArgs (_:args) (n:rest) = n : newArgs args rest -- prefer known tree elements
  -- TODO: Early catch of wrong type
  v <- changeOfTree tree
  case v of
    AChangeObj _ name args ->
      if name == nm then do
        let patArgs = zip pats (newArgs args (argsOfChange tree))
        matches <- mapM (uncurry patMatch) patArgs
        let newTree = treeUnion tree $ TChangeCon (addrOfTree tree) v (M.fromList (zip (map fst args) (map getTree matches)))
        if all isRight matches then
          return $ Right (M.unions (map (\(Right match) -> fst match) matches), newTree)
        else return $ Left newTree
      else return $ Left tree
    AChangeConstr con params ->
      case exprOfCtx con of
        Con conName _ _ ->
         if null pats && nm == conName then return (Right (M.empty, TChangePartialCon (addrOfTree tree) v))
         else return $ Left tree
    _ -> return $ Left tree