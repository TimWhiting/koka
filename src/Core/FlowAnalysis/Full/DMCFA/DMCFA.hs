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
import Core.Core
import Data.Int (Int)
import Common.Name
import Debug.Trace (trace)
import Common.NamePrim (nameOpen, nameEffectOpen, nameHandle, namePerform, nameClause, nameCoreHnd, nameHTag, nameEvvAt, nameMaskAt)
import Data.Maybe (fromJust, isJust)
import Compile.Module (Module(..))
import Common.Failure (HasCallStack)
import Type.Type (splitFunType, typeAny, splitFunScheme, Effect, typeTotal, effectExtend, extractEffectExtend, labelName)
import Control.Monad (foldM, zipWithM, zipWithM_)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)
import Type.Pretty (defaultEnv, ppType)
import Lib.PPrint (hcat, tupled, vcat, text)
import Common.File (startsWith)

mLimit :: FixAAMR r s e Int
mLimit = contextLength <$> getEnv

dLimit :: FixAAMR r s e Int
dLimit = delimContextLength <$> getEnv

drive :: FixAAMR r s e FixChange -> FixAAMR r s e FixChange
drive m = do
  N res <- m
  each [
    return $ N res,
    do
      doStep (Step res)
      doBottom]

doStep :: HasCallStack => FixInput -> FixAAMR r s e FixChange
doStep i =
  memo i $ do
    case i of
      VStore addr ->
        trace ("Value not found in store :" ++ show addr)
        doBottom
      KStore addr -> if addr == endKAddr then return $ KV KEnd else doBottom
      MKStore addr -> if addr == endMKAddr then return $ MKV MKEnd else doBottom
      Step (CEval expr venv kaddr mkaddr ctx) -> do
        drive $ doEval expr venv kaddr mkaddr ctx
      Step (CApply kaddr mkaddr addr ctx) -> do
        drive $ doApply kaddr mkaddr addr ctx
      Step (CUnwind name opName perform kaddr mkaddr addrs ctx) -> do
        drive $ doUnwind name opName perform kaddr mkaddr addrs ctx
      Step CDone -> return $ N CDone

extendStore :: Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  -- trace ("Extending store: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (VStore addr) (SV v)
extendKStore :: Addr -> Kont -> FixAAMR r e s ()
extendKStore addr v = do
  -- trace ("Extending KStore: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (KStore addr) (KV v)
extendMKStore :: Addr -> MKont -> FixAAMR r e s ()
extendMKStore addr v = do
  -- trace ("Extending MKStore: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (MKStore addr) (MKV v)

store addr = do
  SV res <- doStep (VStore addr)
  return res
kStore addr = do
  KV res <- doStep (KStore addr)
  return res
mkStore addr = do
  MKV res <- doStep (MKStore addr)
  return res
eval expr venv kaddr mkaddr ctx = return $ N (CEval expr venv kaddr mkaddr ctx)
apply kaddr mkaddr addr ctx = return $ N (CApply kaddr mkaddr addr ctx)
unwind name opName perform kaddr mkaddr addrs ctx = return $ N (CUnwind name opName perform kaddr mkaddr addrs ctx)

allocConst :: VEnv -> CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst env ctx expr v = do
  let addr = BindImplicitAddr ctx (limitEnv env (fvs expr)) (contextId expr)
  extendStore addr v
  return addr

allocFrame frame kaddr ctx env u = do
  let addr = ImplicitAddr ctx env u
  extendKStore addr (KNext frame (static ctx) kaddr)
  return addr

fvsl :: [ExprContext] -> S.Set TName
fvsl exprs = S.unions $ map fvs exprs

doEval :: HasCallStack => ExprContext -> VEnv -> Addr -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
doEval expr venv kaddr mkaddr ctx =
  trace ("Evaluating: " ++ show expr ++ " in " ++ show (M.toList venv)) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
  case exprOfCtx expr of
    App (TypeApp (Var name _) _) [arg] _ | nameEffectOpen == getName name -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      ch <- childrenContexts expr
      f <- focusChild 1 expr
      eval f venv kaddr mkaddr ctx
    App (TypeApp (Var name _) _) [_,_,f] _ | nameMaskAt == getName name -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      ch <- childrenContexts expr
      f <- focusChild 3 expr
      trace ("Masking " ++ show f) $ return ()
      eval f venv kaddr mkaddr ctx
    Con tn _ _ -> do
      let params = case splitFunScheme (typeOf tn) of
                      Just (_, params, _, _) -> map fst params
                      Nothing -> []
      -- trace ("Con: " ++ show tn ++ " with params: " ++ show params) $ return ()
      let constr = AChangeConstr expr params
      addr <- allocConst venv ctx expr constr
      apply kaddr mkaddr addr (dynamic ctx)
    Var name _ -> do
      if isPrimitive name then do
        addr <- allocConst venv ctx expr (AChangePrim name expr)
        apply kaddr mkaddr addr (dynamic ctx)
      else if qualifier (getName name) == nameCoreHnd then
        error ("Unexpected handler library name in DMCFA: " ++ show name)
      else case lookupEnv name venv of
        Just addr ->
          trace ("Found variable: " ++ show name ++ " at " ++ show addr) $ do
          apply kaddr mkaddr addr (dynamic ctx)
        Nothing -> do
          trace ("Evaluating external: " ++ show name) $ return ()
          res <- bindExternal name
          case res of -- TODO: Evaluate top bindings and store them somewhere, don't re-evaluate based on kaddrs
            Just expr -> do
              extendMKStore (endTopMKAddr name) MKEnd
              each [eval expr M.empty endKAddr (endTopMKAddr name) startCombinedCtx,
                    apply kaddr mkaddr (BindingAddr startCombinedCtx name) (dynamic ctx)]
            Nothing -> do
              trace ("Variable not found: " ++ show name) doBottom
    Lit l -> do
      addr <- allocConst venv ctx expr (injLit l)
      apply kaddr mkaddr addr (dynamic ctx)
    Lam{} -> do
      addr <- allocConst venv ctx expr (AChangeClos expr venv)
      apply kaddr mkaddr addr (dynamic ctx)
    App _ args _ -> doApp args
    Let dgs _ -> do
      bind <- focusLetDefBinding 0 0 expr
      let defGroup = head dgs
      let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
      let defName = defTName (defOfCtx bind)
      k' <- addFrame (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr newEnv) (contextId bind)
      eval bind (limitEnv venv (fvs bind)) k' mkaddr ctx
    -- TODO: Let and case
    TypeApp{} -> do
      e <- focusChild 0 expr
      eval e venv kaddr mkaddr ctx
    TypeLam _ Lam{} -> do
      addr <- allocConst venv ctx expr (AChangeClos expr venv)
      apply kaddr mkaddr addr (dynamic ctx)
    TypeLam _ (App _ args _) -> doApp args
    TypeLam _ _ -> do --(TypeApp Var{} _)
      childs <- childrenContexts expr
      -- trace ("TypeLam: " ++ show (map contextId childs)) $ return ()
      e <- focusChild 0 expr
      eval e venv kaddr mkaddr ctx
    Case _ brs -> do
      s <- focusScrutinee expr
      branches <- mapM (\i -> focusBranch i expr) [0..length brs - 1]
      k' <- addFrame (FScrut expr branches venv) (contextId s)
      eval s (limitEnv venv (fvs s)) k' mkaddr ctx
    -- TypeLam _ e -> do
    --   trace ("TypeLam not handled yet: " ++ show e) $ doBottom
  where addFrame f u = allocFrame f kaddr ctx venv u
        doApp args = do
          f <- focusFun expr
          argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
          k' <- addFrame (FApp (length args) argExprs [] expr venv) (contextId f)
          eval f (limitEnv venv (fvs f)) k' mkaddr ctx

mEnvOf :: AChange -> FixAAMR r s e VEnv
mEnvOf (AChangeClos _ env) = return env
mEnvOf (AChangeKont _ _ env _) = return env
mEnvOf (AChangeObj _ args) = do
  objs <- mapM (store . snd) args
  envs <- mapM mEnvOf objs
  return $ M.unions envs
mEnvOf _ = return M.empty

doApply :: HasCallStack => Addr -> Addr -> Addr -> DynamicCtx -> FixAAMR r s e FixChange
doApply kaddr mkaddr addr dynctx = do
  -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show mkaddr) $ return ()
  k <- kStore kaddr
  -- trace ("Applying: " ++ show k) $ return ()
  case k of
    KEnd -> do
      mk <- mkStore mkaddr
      case mk of
        MKEnd -> do
          if mkaddr == endMKAddr then do
            endV <- store addr
            extendStore endVAddr endV
            return $ N CDone
          else do
            topV <- store addr
            let ImplicitAddr _ env _  = mkaddr
            -- trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
            let [(tname, ctx)] = M.toList env
            extendStore (BindingAddr ctx tname) topV
            return $ N CDone
        MKHandle _ knext mknext _ _ dynctx ->
          apply knext mknext addr (dynamic dynctx)
    KNext frame ctx knext ->
      let newctx = CombinedCtx ctx dynctx
          addFrame f venv u = allocFrame f knext newctx venv u in
      case frame of
        FApp n args res u venv -> do
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
                    let newCtx = CombinedCtx (take m $ CallApp (contextId u) : static newctx) (dynamic newctx)
                    let newEnv = foldl (\acc x -> M.insert x newCtx acc) cenv args
                    -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show args) $ return ()
                    zipWithM_ (\a p -> do
                      val <- store p
                      extendStore (fromJust $ lookupEnv a newEnv) val) args arguments
                    k' <- kStore knext
                    let ia = ImplicitAddr newCtx newEnv (contextId body)
                    extendKStore ia k'
                    eval body (limitEnv newEnv (fvs body)) ia mkaddr newCtx
                  AChangePrim name pms -> do
                    args <- mapM store arguments
                    let addr = BindImplicitAddr newctx venv (contextId u)
                    let n = getName name
                    if isClauseName n || n == nameHTag || n == nameEvvAt then do
                      extendStore addr (AChangeObj name (zip (repeat nameNil) arguments))
                      apply knext mkaddr addr dynctx
                    else if isNamePerform n then do
                      let label = case exprOfCtx u of
                            App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 2))
                            _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
                      let AChangeClos select senv = args !! 1
                      let DefCNonRec _ _ opName = select
                      let opN = newName $ nameLocalQual (getName opName)
                      trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
                      doUnwind label opN u knext mkaddr (drop 2 arguments) newctx
                    else if n == nameHandle then do
                      args <- mapM store arguments
                      let [AChangeObj _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] = args
                      let label = case exprOfCtx u of
                            App (TypeApp _ [_, _, _, h, _]) _ _ -> labelName h
                      d <- dLimit
                      henv <- mEnvOf hnd
                      trace ("OPS " ++ show henv) $ return ()
                      let newCtx = CombinedCtx [] (take d $ (contextId u, ctx):dynctx)
                      bod <- focusBody body
                      -- MKHandle { eff :: Name, mkKNext:: Addr, mknext:: Addr, hnd :: ExprContext, henv :: VEnv, mkCtx:: CombinedCtx }
                      let mk' = ImplicitAddr newCtx venv (contextId u)
                      extendMKStore mk' (MKHandle label knext mkaddr (Handler (arguments !! 1) ret body) (M.unions [retenv, henv]) newCtx)
                      trace ("Applying handle: " ++ show label ++ " with env " ++ show venv) $ return ()
                      eval bod (limitEnv bodyenv (fvs body)) endKAddr mk' newCtx
                    else do
                      res <- doPrimitive n args venv
                      extendStore addr res
                      apply knext mkaddr addr dynctx
                  AChangeConstr con params -> do
                    let name = case exprOfCtx con of
                          Con n _ _ -> n
                          _ -> error "Expected a constructor"
                    let addr = BindImplicitAddr newctx venv (contextId u)
                    extendStore addr (AChangeObj name (zip params arguments))
                    apply knext mkaddr addr dynctx
                  AChangeKont label kx henv hnd -> do
                    m <- mLimit
                    d <- dLimit
                    let newCtx = CombinedCtx (take m $ CallApp (contextId u) : static newctx) (dynamic newctx)
                        newDynCtx = take d $ (contextId u, static newCtx):dynamic newctx
                        mk' = ImplicitAddr newCtx venv (contextId u)
                    extendMKStore mk' (MKHandle label knext mkaddr hnd henv newCtx)
                    apply kx mk' addr newDynCtx
                  _ -> do
                    trace ("Applying non function: " ++ show res) doBottom
            next:rest -> do
              k' <- addFrame (FApp n rest (res ++ [addr]) u (limitEnv venv (fvsl rest))) venv (contextId next)
              eval next (limitEnv venv (fvs next)) k' mkaddr newctx
        FLet groupIdx numGroups bindingIdx numBindings name resolved u venv -> do
          val <- store addr
          trace ("Binding " ++ show name ++ " to " ++ show val) $ return ()
          extendStore (fromJust $ lookupEnv name venv) val
          -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
          if isLetDefBindingFinished groupIdx bindingIdx u then do
            body <- focusLetBod u
            eval body (limitEnv venv (fvs body)) knext mkaddr newctx
          else do
            next <- focusLetDefBinding groupIdx bindingIdx u
            let nextEnv = limitEnv venv (fvs next)
            k' <- addFrame (nextLetFrame frame newctx) nextEnv (contextId next)
            eval next nextEnv k' mkaddr newctx
        FScrut parent branches env -> do
          let recur [] = doBottom
              recur ((branch, expr):branches) = do
                match <- branchMatch branch addr
                case match of
                  Just bindings -> do
                    let newEnv = foldl (\acc tname -> M.insert tname newctx acc) env (M.keys bindings)
                    mapM_ (\(tname, extend) ->
                      extend (fromJust $ lookupEnv tname newEnv)
                      ) (M.toList bindings)
                    eval expr (limitEnv newEnv (fvs expr)) knext mkaddr newctx
                  Nothing -> recur branches
          case exprOfCtx parent of
            Case _ pats -> recur (zip pats branches)
        FHLink eff perform k' h henv -> do
          let ia = ImplicitAddr newctx henv perform
          extendMKStore ia (MKHandle eff knext mkaddr h henv newctx)
          apply k' ia addr dynctx
        _ -> trace ("Applying unknown frame: " ++ show frame) doBottom

doUnwind :: HasCallStack => Name -> Name -> ExprContext -> Addr -> Addr -> [Addr] -> CombinedCtx -> FixAAMR r s e FixChange
doUnwind name opName performExpr kaddr mkaddr args ctx = do
  mk <- mkStore mkaddr
  case mk of
    MKEnd -> error ("Unwind: No MKont found for " ++ show name ++ " " ++ show performExpr)
    MKHandle eff mkKNext mknext h@(Handler hnd ret body) henv mkCtx -> do
      if eff == name then do
        AChangeObj tname hndargs@(_:ops) <- store hnd
        hargs <- mapM (store . snd) hndargs
        trace ("Unwinding: " ++ show (map fst ops) ++ " " ++ show opName ++ " " ++ show hargs) $ return ()
        let unmakeHidden ('-':rest) = newName rest
            unmakeHidden (_:rest) = unmakeHidden rest
        let ops' = map (\(n, a) -> (unmakeHidden $ nameStem n, a)) ops
        case lookup opName ops' of
          Nothing ->
            trace ("Unwind: Operation " ++ show opName ++ " not found in " ++ show ops')
            doBottom
          Just op -> do
            o <- store op
            trace ("Unwinding operation: " ++ show opName ++ " with " ++ show o) $ return ()
            AChangeObj _ [opAddr] <- store op
            AChangeClos op _ <- store (snd opAddr)
            let params = lamNames op
            bod <- focusBody op
            let newEnv = foldl (\acc x -> M.insert x mkCtx acc) henv params
            trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (BindingAddr mkCtx) params)
            extendStore (BindingAddr mkCtx (last params)) (AChangeKont name kaddr henv h)
            eval bod (limitEnv newEnv (fvs bod)) mkKNext mknext mkCtx
      else do
        let k' = ImplicitLAddr ctx henv (contextId performExpr)
        extendKStore k' (KNext (FHLink eff (contextId performExpr) kaddr h henv) (static ctx) mkKNext)
        unwind name opName performExpr k' mknext args mkCtx


branchMatch :: Branch -> Addr -> FixAAMR r s e (Maybe (Bindings r s e))
branchMatch branch addr =
  patMatch (head $ branchPatterns branch) addr

type Bindings r s e = M.Map TName (Addr -> FixAAMR r s e ())

rebind :: Addr -> Addr -> FixAAMR r s e ()
rebind oldAddr newAddr = do
  v <- store oldAddr
  extendStore newAddr v

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
      if patSubsumed plit litChange then return $ Just M.empty
      else return Nothing
    _ -> return Nothing
patMatch (PatCon nm pats _ _ _ _ _ _) addr = do
  -- TODO: Early catch of wrong type
  v <- store addr
  case v of
    AChangeObj name args ->
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

