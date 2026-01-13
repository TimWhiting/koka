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
import qualified Core.FlowAnalysis.StaticContext as SC
import Data.Either (isRight)


-- rebindFrame :: HasCallStack => Frame -> CombinedCtx -> FixAAMR r s e ()
-- rebindFrame frame newCtx = do 
--   expr' <- frameNextExpr frame
--   rebindAll (nextAndFvs expr') (frameCtx frame) newCtx

doStep :: HasCallStack => FixInput -> FixAAMR r s e FixChange
doStep i =
  memo i $ do
    case i of
      VStore UnitAddr -> return $ SV changeUnit
      VStore addr ->
        error ("Value not found in store :" ++ show addr)
        doBottom
      KStore addr -> if addr == EndKAddr then return $ KV EndKAddr else doBottom
      Step (CEval expr ctx) -> doEval expr ctx
      Step (CApply kaddr addr ctx) -> doApply kaddr addr ctx
      Step (CHandleEffects res bodId hnd retCtx) -> doHandleEffects res bodId hnd retCtx
      Step (CHandleLocal res bodId varName valAddr retCtx) -> doHandleLocal res bodId varName valAddr retCtx

extendStore :: Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  -- case addr of
    -- BindImplicitAddr{} -> trace ("Extending implicit store: " ++ show addr ++ " with " ++ show v) $ return ()
    -- ConImplicitAddr{} -> return ()
    -- _ -> trace ("Extending store: " ++ show addr ++ " with " ++ show v) $ return ()
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
eval :: HasCallStack => ExprContext -> CombinedCtx -> FixAAMR r s e RValue
eval expr ctx = unreturnV $ doStep $ Step (CEval expr ctx)
apply :: HasCallStack => Addr -> Addr -> DynamicCtx -> FixAAMR r s e RValue
apply kaddr addr ctx = unreturnV $ doStep $ Step (CApply kaddr addr ctx)
handleEffects :: HasCallStack => RValue -> ExprContextId -> Handler -> CombinedCtx -> FixAAMR r s e RValue
handleEffects res bodId hnd retCtx = unreturnV $ doStep $ Step (CHandleEffects res bodId hnd retCtx)
handleLocal :: HasCallStack => RValue -> ExprContextId -> TName -> Addr -> CombinedCtx -> FixAAMR r s e RValue
handleLocal res bodId varName valAddr retCtx = unreturnV $ doStep $ Step (CHandleLocal res bodId varName valAddr retCtx)
returnConst :: CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e FixChange
returnConst ctx expr v = RV . RVAddr <$> allocConst ctx expr v
returnAddr :: Addr -> FixAAMR r s e FixChange
returnAddr addr = return $ RV $ RVAddr addr
returnOp :: DelimitedVal -> StaticCtx -> Frame ->  DelimitedFrame -> Addr -> FixAAMR r s e FixChange
returnOp dval ctx frame dframe kaddr = return $ RV $ ROp dval ctx frame dframe kaddr

allocConst :: CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst ctx expr v = do
  let addr = BindImplicitAddr ctx (contextId expr)
  extendStore addr v
  return addr

rebindAll :: HasCallStack => S.Set TName -> CombinedCtx -> CombinedCtx -> FixAAMR r s e ()
rebindAll free oldCtx newCtx = do
  if oldCtx == newCtx then return ()
  else
    -- trace ("Rebinding all from " ++ show oldCtx ++ " to " ++ show newCtx ++ " for " ++ show (S.toList free)) $
    mapM_ (\fv -> rebind (BindingAddr oldCtx fv) (BindingAddr newCtx fv)) free

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
        App (Var nm _) _ _ | isConstructorName (getName nm) || getName nm `elem` [nameHTag, nameEvvAt, nameSSizeT] -> True
        App (TypeApp (Var nm _) _) _ _ | isConstructorName (getName nm) || getName nm `elem` [nameHTag, nameEvvAt, nameSSizeT] -> True
        App (App (TypeApp (Var nm _) _) [e] _) _ _ -> getName nm == nameEffectOpen
        -- App e _ _ -> isSimpleExpr e
        _ -> False -- Essentially just Let / Case
      process x = if not open && not (isSimpleExpr (exprOfCtx expr)) then do
                    -- analysisLog ("Evaluating: " ++ show (ppContextPath expr) ++ "\n" ++ showCtxExpr expr ++ "\n:" ++ show ctx)
                    res <- x
                    -- analysisLog (" Result: " ++ show (ppContextPath expr) ++ "\n" ++ show res)
                    return res
                  else x-- trace ("Evaluating: " ++ show expr ++ " in " ++ show (M.toList venv) ++ " : " ++ show ctx) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
   in process $ case exprOfCtx expr of
    App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen || getName name == namePretendDecreasing -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      returnV $ eval f ctx
    App (TypeApp (Var name _) _) [_,_,f] _ | getName name == nameMaskAt -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 3 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f ctx
      doContinue res FMask ctx
    App (TypeApp (Var name _) _) [f] _ | getName name == nameMaskBuiltin -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      -- trace ("Masking " ++ show f) $ return ()
      res <- eval f ctx
      doContinue res FMask ctx
    Con tn _ _ -> do
      let params = case splitFunScheme (typeOf tn) of
                      Just (_, params, _, _) -> map fst params
                      Nothing -> []
      -- trace ("Con: " ++ show tn ++ " with params: " ++ show params) $ return ()
      let constr = AChangeConstr expr params
      returnConst ctx expr constr
    Var name _ -> do
      if isPrimitive name && not (isTrickyPrimitive name) then do
        -- trace ("Primitive " ++ show name) $ return ()
        returnConst ctx expr (AChangePrim name expr)
      else if qualifier (getName name) == nameCoreHnd then
        error ("Unexpected handler library name in DMCFA: " ++ show name)
      else if qualifier (getName name) == nameNil then do
        -- trace ("Found variable: " ++ show name ++ " at " ++ show name) $ return ()
        returnAddr (BindingAddr ctx name)
      else do
        -- trace ("Evaluating external: " ++ show name) $ return ()
        res <- bindExternal (equalPrimitive name)
        case res of
          Just expr -> do
            c <- startCombinedCtx
            returnV $ eval expr c
          Nothing -> trace ("Variable not found: " ++ show name) doBottom
    Lit l -> returnConst ctx expr (injLit (contextId expr) l)
    Lam{} -> returnConst ctx expr (AChangeClos expr ctx)
    App _ args _ -> doApp args
    Let dgs _ -> doLet dgs
    TypeApp{} -> do
      e <- focusChild 0 expr
      returnV $ eval e ctx
    TypeLam _ Lam{} -> returnConst ctx expr (AChangeClos expr ctx)
    TypeLam _ (App _ args _) -> doApp args
    TypeLam _ (Let dgs _) -> doLet dgs
    TypeLam _ _ -> do --(TypeApp Var{} _)
      childs <- childrenContexts expr
      -- trace ("TypeLam: " ++ show (map contextId childs)) $ return ()
      e <- focusChild 0 expr
      returnV $ eval e ctx
    Case _ brs -> do
      s <- focusScrutinee expr
      branches <- mapM (\i -> focusBranch i expr) [0..length brs - 1]
      -- trace (show branches) $ return ()
      res <- eval s ctx
      doContinue res (FScrut expr branches ctx) ctx
    -- TypeLam _ e -> do
    --   trace ("TypeLam not handled yet: " ++ show e) $ doBottom
  where 
    doLet dgs = do
          child <- childrenContexts expr
          -- trace ("LetChildren: " ++ intercalate "\n" (map show child)) $ return ()
          bind <- focusLetDefBinding 0 0 expr
          let defGroup = head dgs
          -- let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) (defsOf defGroup)
          let defName = defTName (defOfCtx bind)
          -- trace ("Let binding: " ++ show defName ++ " in " ++ show newEnv) $ return ()
          res <- eval bind ctx
          doContinue res (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr ctx) ctx
    doApp args = do
          f <- focusFun expr
          argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
          -- trace ("Applying function: " ++ show f ++ " to args: " ++ show argExprs ++ " with env " ++ show venv) $ return ()
          res <- eval f ctx
          doContinue res (FApp (length args) argExprs [] expr ctx) ctx


doContinue :: HasCallStack => RValue -> Frame -> CombinedCtx -> FixAAMR r s e FixChange
doContinue res frame ctx =
  -- trace ("Continuing with\nFrame:" ++ show frame ++ "\nResult:\n"  ++ show res ++  "\n:" ++ show ctx) $
  case res of
    ROp dval ctx' frame' dframe knext -> do
      let k' = KAddr frame' ctx' dframe dval
      extendKStore k' knext
      returnOp dval (static ctx) frame dframe k'
    RVAddr addr -> do
      case frame of
          FrameDone -> returnAddr addr
          f | f == FMask -> do -- TODO: Implement proper masking
            v <- store addr
            case v of
              AChangeClos e env -> do
                bod <- focusBody e
                rebindAll (fvvs e) env ctx
                returnV $ eval bod ctx
          FApp n args res eApp oldCtx -> do
            let uApp = contextId eApp
            case args of
              [] -> case res ++ [addr] of
                f:arguments -> do
                  res <- store f
                  case res of
                    AChangeClos cexpr cenv -> do
                      body <- focusBody cexpr
                      let params = lamNames cexpr
                      m <- mLimit
                      let newCtx = addCall m ctx uApp
                      -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show (f:arguments)) $ return ()
                      zipWithM_ (\p a -> rebind a (BindingAddr newCtx p)) params arguments
                      rebindAll (fvvs cexpr) cenv newCtx
                      returnV $ eval body newCtx
                    AChangePrim name pms -> do
                      let retAddr = BindImplicitAddr ctx uApp
                      let n = getName name
                      if not (isHandlerPrimitive n) then do
                        args <- mapM store arguments
                        res <- doPrimitive n args store
                        extendStore retAddr res
                        returnAddr retAddr
                      else doHandlerPrimitive name n retAddr arguments ctx eApp
                    AChangeConstr con params -> do
                      let name = case exprOfCtx con of
                            Con n _ _ -> n
                            _ -> error "Expected a constructor"
                      let retAddr = BindImplicitAddr ctx uApp
                      let conParams = map (\nm -> ConImplicitAddr nm ctx uApp) params
                      zipWithM_ rebind arguments conParams
                      extendStore retAddr (AChangeObj con name (zip params conParams))
                      -- extendStore addr (AChangeObj con name (zip params arguments))
                      returnAddr retAddr
                    AChangeKont kx hctx hnd -> do
                      m <- mLimit
                      d <- dLimit
                      let newCtx = addCall m ctx uApp
                          newDynCtx = addDelim d newCtx uApp (hLabel hnd)
                      -- trace ("Applying continuation\n" ++ show uApp ++ "\n" ++ show newCtx ++ "\n" ++ show newDynCtx) $ return () -- ++ "for\n" ++
                      res <- apply kx addr newDynCtx
                      returnV $ handleEffects res uApp hnd newCtx
                    _ -> do
                      trace ("Applying non function: " ++ show res) doBottom
              next:rest -> do
                -- trace ("Adding addr " ++ show addr ++ " next " ++ show next) $ return ()
                rebindAll (nextAndFvs next) oldCtx ctx
                ret <- eval next ctx
                doContinue ret (FApp n rest (res ++ [addr]) eApp ctx) ctx
          FLet groupIdx numGroups bindingIdx numBindings name resolved u oldCtx -> do
            -- trace ("Applying Let " ++ show addr ++ " " ++ show (BindingAddr ctx name)) $ return ()
             -- We need to override the old name binding (in case it was in a different context)
            rebind addr (BindingAddr ctx name)
            -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show venv ) $ return ()
            -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
            if isLetDefBindingFinished groupIdx bindingIdx u then do
              -- trace ("Let group finished: " ++ show groupIdx ++ " of " ++ show numGroups) $ return ()
              body <- focusLetBod u
              rebindAll (S.delete name $ fvvs body) oldCtx ctx
              returnV $ eval body ctx
            else do
              -- trace ("Let group next: " ++ show groupIdx ++ ", " ++ show bindingIdx) $ return ()
              next <- focusNextLetDefBinding groupIdx bindingIdx u
              rebindAll (S.delete name $ nextFvs next) oldCtx ctx
              ret <- eval next ctx
              doContinue ret (nextLetFrame frame ctx) ctx
          FScrut parent branches oldCtx -> do
            let recur [] tree = doBottom
                recur ((branch, br):branches) tree = do
                  match <- branchMatch br branch tree ctx
                  case match of
                    Right (bindings, matchTree) -> do
                      -- trace ("Match " ++ show (M.keys bindings)) $ return ()
                      mapM_ (\(tname, extend) ->
                        extend (BindingAddr ctx tname)
                        ) (M.toList bindings)
                      body <- focusBranchExpr br
                      rebindAll (S.union (fvvs body) (nextFvs body)) oldCtx ctx
                      each [
                        returnV $ eval body ctx,
                        returnV $ eval br ctx,
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
                  -- let newEnv = M.insert arg ctx cenv
                  rebind addr (BindingAddr ctx arg)
                  rebindAll (fvvs cexpr) cenv ctx
                  returnV $ eval body ctx
          FResume retCtx kont hnd u -> do
            m <- mLimit
            d <- dLimit
            let newRetCtx = addCall m ctx u
                newDelimCtx = addDelim d newRetCtx u (hLabel hnd)
            -- trace ("Applying continuation " ++ show u ++ " " ++ show (hLabel hnd)) $ return ()
            res <- apply kont addr newDelimCtx
            returnV $ handleEffects res u hnd newRetCtx
          _ -> do
            error ("Continuing: " ++ show res ++ " with unknown frame " ++ show frame)

doApply :: HasCallStack => Addr -> Addr -> DynamicCtx -> FixAAMR r s e FixChange
doApply kaddr addr dynctx = do
  -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show dynctx) $ return ()
  case kaddr of
    EndKAddr -> returnAddr addr
    KAddr (FRestoreDelim (DFrameLocal venv bodId varName varAddr)) ctx _ _ -> do
      let newctx = CombinedCtx ctx dynctx
      d <- dLimit
      m <- mLimit
      let newRetCtx = addCall m newctx bodId
      let newDelimCtx = newDelim d m newRetCtx bodId (getName varName)
      knext <- kStore kaddr
      res <- apply knext addr (dynamic newDelimCtx)
      returnV $ handleLocal res bodId varName varAddr newRetCtx
    KAddr (FRestoreDelim (DFrame venv bodId h)) ctx _ _ -> do
      let newctx = CombinedCtx ctx dynctx
      d <- dLimit
      m <- mLimit
      let newRetCtx = addCall m newctx bodId
      let newDelimCtx = newDelim d m newRetCtx bodId (hLabel h)
      knext <- kStore kaddr
      res <- apply knext addr (dynamic newDelimCtx)
      -- trace ("Restoring handler context for " ++ show h ++ " with\n" ++ show newRetCtx ++ "\n" ++ show newDelimCtx ++ "\n") $ return () 
      returnV $ handleEffects res bodId h newRetCtx
    KAddr frame ctx _ _ -> do
      knext <- kStore kaddr
      res <- apply knext addr dynctx
      let newctx = CombinedCtx ctx dynctx
      doContinue res frame newctx
isHandlerPrimitive :: Name -> Bool
isHandlerPrimitive n =
  n == nameHandle || isClauseName n || n == nameHTag
  || n == nameEvvAt || n == nameMaskAt || isNamePerform n || isClauseName n
  || n == nameLocalVar || n == nameLocalGet || n == nameLocalSet

doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> [Addr] -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
doHandlerPrimitive name n addr arguments ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
  extendStore addr (AChangeObj u name (zip (repeat nameNil) arguments))
  returnAddr addr
doHandlerPrimitive name n addr arguments ctx u | isNamePerform n = do
  let label = case exprOfCtx u of
        App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 1))
        _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
  AChangeClos select senv <- store (arguments !! 1)
  let DefCNonRec _ _ opName = select
  let opN = newName $ nameLocalQual (getName opName)
  -- trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
  returnOp (DVal label opN u (drop 2 arguments) ctx) (static ctx) FrameDone DFrameDone EndKAddr
doHandlerPrimitive name n addr arguments ctx u | n == nameLocalGet = do
  -- trace ("LocalGet: " ++ show name ++ " " ++ show n ++ "\n" ++ show (head arguments)) $ return ()
  if localEff then do
    let [varAddr@(BindingAddr _ varName), _] = arguments
    returnOp (DVal (getName varName) nameLocalGet u [] ctx) (static ctx) FrameDone DFrameDone EndKAddr
  else do
    returnAddr (head arguments)
doHandlerPrimitive name n addr arguments ctx u | n == nameLocalSet = do
  let [varAddr@(BindingAddr _ varName), val] = arguments
  -- trace ("LocalSet: " ++ show name ++ " " ++ show n ++ "\n" ++ show args ++ "\n" ++ show arguments) $ return ()
  if localEff then do
    returnOp (DVal (getName varName) nameLocalSet u [val] ctx) (static ctx) FrameDone DFrameDone EndKAddr
  else do
    rebind val varAddr
    extendStore addr changeUnit
    returnAddr addr
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
      -- trace ("Handling: " ++ show label ++ " in " ++ show ctx ++ " " ++ show newctx) $ return ()
      -- trace ("New handler context:\n" ++ showCtxExpr bod ++ "\n") $ return ()
      rebindAll (fvvs body) bodyenv newctx
      res <- eval bod newctx
      let h = Handler label (arguments !! 1) (Just ret) (Just $ FDollar (arguments !! 2))
      returnV $ handleEffects res (contextId bod) h ctx
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
        -- trace ("New local context:\n" ++ show newctx ++ "\n") $ return ()
        rebindAll (fvvs bod) ctx newctx
        res <- eval bod newctx
        returnV $ handleLocal res (contextId bod) varName (head arguments) ctx
  else do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        -- let newEnv = M.insert varName ctx env
        bod <- focusBody e
        rebind (head arguments) (BindingAddr ctx varName)
        returnV $ eval bod ctx
localEff = True

doHandleLocal :: HasCallStack => RValue -> ExprContextId -> TName -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
doHandleLocal res bodId varName valAddr retCtx = do
  case res of
    ROp dval ctx' frame' dframe' knext -> do
      let kOp = KAddr frame' ctx' dframe' dval
      extendKStore kOp knext
      case dval of
        DVal hName opName oExpr args oCtx | hName == getName varName && opName == nameLocalGet -> do
          -- trace ("Getting local variable: " ++ show varName ++ " of " ++ show valAddr) $ return ()
          res <- apply kOp valAddr (dynamic retCtx)
          returnV $ handleLocal res bodId varName valAddr retCtx
        DVal hName opName oExpr [newAddr] oCtx | hName == getName varName && opName == nameLocalSet -> do
          extendStore UnitAddr changeUnit
          d <- dLimit
          m <- mLimit
          let newRetCtx = addCall m retCtx bodId
          let newDelimCtx = newDelim d m newRetCtx bodId (getName varName)
          res <- apply kOp newAddr (dynamic newDelimCtx)
          returnV $ handleLocal res bodId varName newAddr newRetCtx
        DVal hName opName opExpr args oCtx -> do
          -- trace ("Passing along local operation: " ++ show opName ++ " at local " ++ show varName ++ " searching for " ++ show hName) $ return ()
          let dframe = DFrameLocal retCtx bodId varName valAddr
          returnOp dval (static retCtx) (FRestoreDelim dframe) dframe kOp
    RVAddr addr -> returnAddr addr

doHandleEffects :: HasCallStack => RValue -> ExprContextId -> Handler -> CombinedCtx -> FixAAMR r s e FixChange
doHandleEffects res bodId h@(Handler label hnd mbRet mbFrame) retCtx  = do
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
            rebindAll (fvvs op) openv retCtx
            -- let newEnv = foldl (\acc x -> M.insert x retCtx acc) openv params
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (BindingAddr retCtx) params)
            if isTailOpT opConName then do -- TODO: TIM
              res <- eval opBod retCtx
              doContinue res (FResume ctx' kOp h (contextId opBod)) retCtx
            else if isNeverOp opConName then do
              returnV $ eval opBod retCtx
            else do
              extendStore (BindingAddr retCtx (last params)) (AChangeKont kOp retCtx h)
              returnV $ eval opBod retCtx
      else do
        -- trace ("Allocating new return\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n" ++ show label ++ "," ++ show opName ++ "\n") $ return ()
        let k' = KAddr frame' ctx' dframe' dval
        extendKStore k' knext
        let dframe = DFrame retCtx bodId h
        returnOp dval (static retCtx) (FRestoreDelim dframe) dframe k'
    res ->
      case mbFrame of
        Just frame -> do
          -- trace ("Continuing after handling effects\n" ++ show retCtx  ++ "\n" ++ show delimCtx ++ "\n") $ return ()
          doContinue res frame retCtx
        Nothing -> return $ RV res

branchMatch :: ExprContext -> Branch -> AChangeTree -> CombinedCtx -> FixAAMR r s e (Either AChangeTree (Bindings r s e) )
branchMatch branchCtx branch addr ctx = do
  match <- patMatch (head $ branchPatterns branch) addr
  case match of 
    Left tree -> return $ Left tree
    Right (bindings, tree) -> 
      if isExprTrue (guardTest $ head (branchGuards branch)) then return $ Right (bindings, tree)
      else do
        mapM_ (\(tname, extend) ->
          extend (BindingAddr ctx tname)
          ) (M.toList bindings)
        guard <- focusGuardExpr branchCtx
        RVAddr a <- eval guard ctx
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