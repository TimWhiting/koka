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
import Common.File (startsWith)
import Syntax.Syntax (ValueBinder(binderName))
import Data.List (intercalate)

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
      KStore addr -> if addr == EndKAddr then return $ KV KEnd else doBottom
      MKStore addr -> if addr == EndMKAddr then return $ MKV MKEnd else doBottom
      Step (CEval expr venv kaddr mkaddr ctx) -> do
        drive $ doEval expr venv kaddr mkaddr ctx
      Step (CApply kaddr mkaddr addr ctx) -> do
        drive $ doApply kaddr mkaddr addr ctx
      Step (CUnwind name opName perform kaddr mkaddr addrs ctx) -> do
        drive $ doUnwind name opName perform kaddr mkaddr addrs ctx
      Step (CUnwindLookup varName knext mkaddr u ctx) -> do
        drive $ unwindLookup varName knext mkaddr u ctx
      Step (CUnwindSet varName val knext mkaddr addr u ctx) -> do
        drive $ unwindSet varName val knext mkaddr addr u ctx
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
unwind_lookup varName knext mkaddr u ctx = return $ N (CUnwindLookup varName knext mkaddr u ctx)
unwind_set varName val knext mkaddr addr u ctx = return $ N (CUnwindSet varName val knext mkaddr addr u ctx)

allocConst :: VEnv -> StaticCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst env ctx expr v = do
  let addr = BindImplicitAddr ctx (limitEnv env (fvs expr)) (contextId expr)
  extendStore addr v
  return addr

allocFrame frame kaddr ctx env u = do
  let addr = ImplicitAddr ctx env u
  extendKStore addr (KNext frame kaddr)
  return addr

fvsl :: [ExprContext] -> S.Set TName
fvsl exprs = S.unions $ map fvs exprs

primitiveFuncWrappers = [nameUnsafeNoLocalCast, nameUnsafeTotalCast]

doEval :: HasCallStack => ExprContext -> VEnv -> Addr -> Addr -> StaticCtx -> FixAAMR r s e FixChange
doEval expr venv kaddr mkaddr ctx =
  -- trace ("Evaluating: " ++ show expr ++ " in " ++ show (M.toList venv)) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
  case exprOfCtx expr of
    App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      eval f venv kaddr mkaddr ctx
    App (TypeApp (Var name _) _) [_,_,f] _ | getName name == nameMaskAt -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 3 expr
      -- trace ("Masking " ++ show f) $ return ()
      k' <- addFrame FMask (contextId f)
      eval f venv k' mkaddr ctx
    App (TypeApp (Var name _) _) [f] _ | getName name == nameMaskBuiltin -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      -- trace ("Masking " ++ show f) $ return ()
      k' <- addFrame FMask (contextId f)
      eval f venv k' mkaddr ctx
    Con tn _ _ -> do
      let params = case splitFunScheme (typeOf tn) of
                      Just (_, params, _, _) -> map fst params
                      Nothing -> []
      -- trace ("Con: " ++ show tn ++ " with params: " ++ show params) $ return ()
      let constr = AChangeConstr expr params
      addr <- allocConst venv ctx expr constr
      apply kaddr mkaddr addr ctx
    Var name _ -> do
      if isPrimitive name then do
        -- trace ("Primitive " ++ show name) $ return ()
        addr <- allocConst venv ctx expr (AChangePrim name expr)
        apply kaddr mkaddr addr ctx
      else if qualifier (getName name) == nameCoreHnd then
        error ("Unexpected handler library name in DMCFA: " ++ show name)
      else case lookupEnv name venv of
        Just addr ->
          -- trace ("Found variable: " ++ show name ++ " at " ++ show addr) $ do
          apply kaddr mkaddr addr ctx
        Nothing -> do
          -- trace ("Evaluating external: " ++ show name) $ return ()
          res <- bindExternal name
          case res of -- TODO: Evaluate top bindings and store them somewhere, don't re-evaluate based on kaddrs
            Just expr -> do
              extendMKStore (TopAddr name) MKEnd
              c <- startStaticCtx
              each [eval expr M.empty EndKAddr (TopAddr name) c,
                    apply kaddr mkaddr (BindingAddr c name) ctx]
            Nothing -> do
              trace ("Variable not found: " ++ show name) doBottom
    Lit l -> do
      addr <- allocConst venv ctx expr (injLit (contextId expr) l)
      apply kaddr mkaddr addr ctx
    Lam{} -> do
      -- trace ("Allocating closure " ++ show expr ++ " " ++ show venv) $ return ()
      addr <- allocConst venv ctx expr (AChangeClos expr venv)
      apply kaddr mkaddr addr ctx
    App _ args _ -> doApp args
    Let dgs _ -> do
      child <- childrenContexts expr
      -- trace ("LetChildren: " ++ intercalate "\n" (map show child)) $ return ()
      bind <- focusLetDefBinding 0 0 expr
      let defGroup = head dgs
      let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
      let defName = defTName (defOfCtx bind)
      -- trace ("Let binding: " ++ show defName ++ " in " ++ show newEnv) $ return ()
      k' <- addFrame (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr newEnv) (contextId bind)
      eval bind (limitEnv newEnv (S.insert defName (fvs bind)) ) k' mkaddr ctx
    -- TODO: Let and case
    TypeApp{} -> do
      e <- focusChild 0 expr
      eval e venv kaddr mkaddr ctx
    TypeLam _ Lam{} -> do
      addr <- allocConst venv ctx expr (AChangeClos expr venv)
      apply kaddr mkaddr addr ctx
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
mEnvOf (AChangeObj _ _ args) = do
  objs <- mapM (store . snd) args
  envs <- mapM mEnvOf objs
  return $ M.unions envs
mEnvOf _ = return M.empty

doApply :: HasCallStack => Addr -> Addr -> Addr -> StaticCtx -> FixAAMR r s e FixChange
doApply kaddr mkaddr addr ctx = do
  -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show mkaddr) $ return ()
  k <- kStore kaddr
  -- trace ("Applying: " ++ show k) $ return ()
  case k of
    KEnd -> do
      mk <- mkStore mkaddr
      case mk of
        MKEnd -> do
          if mkaddr == EndMKAddr then do
            endV <- store addr
            extendStore EndVAddr endV
            return $ N CDone
          else do
            topV <- store addr
            let TopAddr name = mkaddr
            c <- startStaticCtx
            -- trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
            extendStore (BindingAddr c name) topV
            return $ N CDone
        MKHandle _ knext mknext _ _ ->
          apply knext mknext addr ctx
    KNext frame knext ->
      -- trace ("Applying " ++ show frame) $ 
      let addFrame f venv u = allocFrame f knext ctx venv u in
      case frame of
        f | f == FCall || f == FMask -> do
          v <- store addr
          case v of
            AChangeClos e env -> do
              bod <- focusBody e
              -- trace ("Applying FMask " ++ show env) $ return()
              eval bod env knext mkaddr ctx
        FDollar va dollarH -> do 
          mk <- mkStore mkaddr
          case mk of
            MKEnd -> doBottom
            MKHandle _ knext mknext _ dynctx -> do
              res <- store va
              case res of 
                AChangeClos cexpr cenv -> do
                    body <- focusBody cexpr
                    let [arg] = lamNames cexpr
                    k <- kLimit
                    let newCtx = take k $ CallApp dollarH : ctx
                    let newEnv = M.insert arg newCtx cenv
                    -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show arg) $ return ()
                    v <- store addr
                    extendStore (fromJust $ lookupEnv arg newEnv) v
                    eval body (limitEnv newEnv (fvs body)) knext mknext newCtx
        FResume label kont venv hnd u -> do
          k <- kLimit
          let newCtx = take k $ CallApp u : ctx
              mk' = ImplicitAddr newCtx venv u
          -- trace ("Applying continuation " ++ show (contextId u) ++ " " ++ show henv ) $ return () -- ++ "for\n" ++ 
          extendMKStore mk' (MKHandle label knext mkaddr hnd venv)
          apply kont mk' addr ctx
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
                    k <- kLimit
                    let newCtx = take k $ CallApp (contextId u) : ctx
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
                    let addr = BindImplicitAddr ctx venv (contextId u)
                    let n = getName name
                    if isHandlerPrimitive n then
                      doHandlerPrimitive name n addr knext mkaddr arguments venv ctx u
                    else do
                      args <- mapM store arguments
                      res <- doPrimitive n args
                      extendStore addr res
                      apply knext mkaddr addr ctx
                  AChangeConstr con params -> do
                    let name = case exprOfCtx con of
                          Con n _ _ -> n
                          _ -> error "Expected a constructor"
                    let addr = BindImplicitAddr ctx venv (contextId u)
                    extendStore addr (AChangeObj con name (zip params arguments))
                    apply knext mkaddr addr ctx
                  AChangeKont label kx henv hnd -> do
                    k <- kLimit
                    let newCtx = take k $ CallApp (contextId u) : ctx
                        mk' = ImplicitAddr ctx venv (contextId u)
                    extendMKStore mk' (MKHandle label knext mkaddr hnd (M.union venv henv))
                    apply kx mk' addr newCtx
                  _ -> do
                    trace ("Applying non function: " ++ show res) doBottom
            next:rest -> do
              k' <- addFrame (FApp n rest (res ++ [addr]) u (limitEnv venv (fvsl rest))) venv (contextId next)
              eval next (limitEnv venv (fvs next)) k' mkaddr ctx
        FLet groupIdx numGroups bindingIdx numBindings name resolved u venv -> do
          -- trace "Applying Let" $ return ()
          val <- store addr
          -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show venv ) $ return ()
          extendStore (fromJust $ lookupEnv name venv) val
          -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
          if isLetDefBindingFinished groupIdx bindingIdx u then do
            body <- focusLetBod u
            eval body (limitEnv venv (fvs body)) knext mkaddr ctx
          else do
            next <- focusLetDefBinding groupIdx bindingIdx u
            k' <- addFrame (nextLetFrame frame ctx) venv (contextId next)
            eval next venv k' mkaddr ctx
        FScrut parent branches env -> do
          let recur [] = doBottom
              recur ((branch, expr):branches) = do
                match <- branchMatch branch addr
                case match of
                  Just bindings -> do
                    let newEnv = foldl (\acc tname -> M.insert tname ctx acc) env (M.keys bindings)
                    mapM_ (\(tname, extend) ->
                      extend (fromJust $ lookupEnv tname newEnv)
                      ) (M.toList bindings)
                    eval expr (limitEnv newEnv (fvs expr)) knext mkaddr ctx
                  Nothing -> recur branches
          case exprOfCtx parent of
            Case _ pats -> recur (zip pats branches)
        FHLink eff perform k' h henv -> do
          let ia = ImplicitLRAddr ctx eff henv perform
          extendMKStore ia (MKHandle eff knext mkaddr h henv)
          apply k' ia addr ctx
        _ -> trace ("Applying unknown frame: " ++ show frame) doBottom

doUnwind :: HasCallStack => Name -> Name -> ExprContext -> Addr -> Addr -> [Addr] -> StaticCtx -> FixAAMR r s e FixChange
doUnwind name opName performExpr kaddr mkaddr args ctx = do
  mk <- mkStore mkaddr
  case mk of
    MKEnd -> doBottom -- error ("Unwind: No MKont found for " ++ show name ++ " " ++ show performExpr)
    MKHandle eff mkKNext mknext h@(Handler hnd ret) henv -> do
      if eff == name then do
        AChangeObj _ tname hndargs@(_:ops) <- store hnd
        hargs <- mapM (store . snd) hndargs
        -- trace ("Unwinding: " ++ show (map fst ops) ++ " " ++ show opName ++ " " ++ show hargs) $ return ()
        let unmakeHidden ('@':'v':'a':'l':'-':op) = opName
            unmakeHidden ('-':rest) = newName rest
            unmakeHidden (_:rest) = unmakeHidden rest
        let ops' = map (\(n, a) -> (unmakeHidden $ nameStem n, a)) ops
        case lookup opName ops' of
          Nothing ->
            -- trace ("Unwind: Operation " ++ show opName ++ " not found in " ++ show ops')
            doBottom
          Just op -> do
            o <- store op
            k <- kLimit
            let newCtx = take k $ CallApp (contextId performExpr) : ctx
            -- trace ("Unwinding operation: " ++ show opName ++ " with " ++ show o) $ return ()
            AChangeObj _ opConName [opAddr] <- store op
            AChangeClos op openv <- store (snd opAddr)
            let params = lamNames op
            bod <- focusBody op
            let newEnv = foldl (\acc x -> M.insert x newCtx acc) openv params
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (BindingAddr newCtx) params)
            -- extendStore (BindingAddr ctx (last params)) (AChangeKont name kaddr henv h)
            -- eval bod (limitEnv newEnv (fvs bod)) mkKNext mknext ctx
            if nameStem (getName opConName) `startsWith` "clause-tail" then do
              let k' = ImplicitAddr newCtx henv (contextId bod)
              extendKStore k' (KNext (FResume eff kaddr henv h (contextId bod)) mkKNext)
              eval bod (limitEnv newEnv (fvs bod)) k' mknext newCtx
            else if nameStem (getName opConName) `startsWith` "clause-never" then do 
              eval bod (limitEnv newEnv (fvs bod)) mkKNext mknext newCtx
            else do
              extendStore (BindingAddr newCtx (last params)) (AChangeKont name kaddr henv h)
              eval bod (limitEnv newEnv (fvs bod)) mkKNext mknext newCtx
      else do
        let k' = ImplicitLAddr ctx eff henv (contextId performExpr)
        extendKStore k' (KNext (FHLink eff (contextId performExpr) kaddr h henv) mkKNext)
        unwind name opName performExpr k' mknext args ctx


unwindLookup :: HasCallStack => TName -> Addr -> Addr -> ExprContext -> StaticCtx -> FixAAMR r s e FixChange
unwindLookup varName knext mkaddr u ctx = do
  mk <- mkStore mkaddr
  case mk of
    MKHandle nm k' mknext h venv | getName varName == nm -> do
      let Just varAddr = lookupEnv varName venv
      apply knext mkaddr varAddr ctx
    MKHandle nm k' mknext h venv -> do
      let kx = ImplicitLAddr ctx nm venv (contextId u)
      extendKStore kx (KNext (FHLink nm (contextId u) knext h venv) k')
      unwind_lookup varName kx mknext u ctx   
    _ -> doBottom


unwindSet :: HasCallStack => TName -> Addr -> Addr -> Addr -> Addr -> ExprContext -> StaticCtx -> FixAAMR r s e FixChange
unwindSet varName val knext mkaddr addr u ctx = do
  mk <- mkStore mkaddr
  case mk of
    MKHandle nm k' mknext h venv | getName varName == nm -> do
      let env = M.delete varName venv
      k <- kLimit
      v <- store val
      let u = vcontextId v
      let newctx = take k $ CallApp u : ctx
      let newEnv = M.insert varName newctx env
      rebind val (fromJust $ lookupEnv varName newEnv) 
      let mk' = ImplicitAddr newctx newEnv u
      extendMKStore mk' (MKHandle nm k' mknext h newEnv)
      extendStore addr changeUnit
      apply knext mk' addr newctx
    MKHandle nm k' mknext h venv -> do
      let kx = ImplicitLAddr ctx nm venv (contextId u)
      extendKStore kx (KNext (FHLink nm (contextId u) knext h venv) k')
      unwind_set varName val kx mknext addr u ctx
    _ -> doBottom

isHandlerPrimitive :: Name -> Bool
isHandlerPrimitive n =
  n == nameHandle || isClauseName n || n == nameHTag
  || n == nameEvvAt || n == nameMaskAt || isNamePerform n || isClauseName n
  || n == nameLocalVar || n == nameLocalGet || n == nameLocalSet

doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> Addr -> Addr -> [Addr] -> VEnv -> StaticCtx -> ExprContext -> FixAAMR r s e FixChange
doHandlerPrimitive name n addr knext mkaddr arguments venv ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
  extendStore addr (AChangeObj u name (zip (repeat nameNil) arguments))
  apply knext mkaddr addr ctx
doHandlerPrimitive name n addr knext mkaddr arguments venv ctx u | isNamePerform n = do
  args <- mapM store arguments
  let label = case exprOfCtx u of
        App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 1))
        _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
  let AChangeClos select senv = args !! 1
  let DefCNonRec _ _ opName = select
  let opN = newName $ nameLocalQual (getName opName)
  -- trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
  doUnwind label opN u knext mkaddr (drop 2 arguments) ctx
doHandlerPrimitive name n addr knext mkaddr arguments venv ctx u | n == nameLocalGet = do
  -- trace ("LocalGet: " ++ show name ++ " " ++ show n ++ "\n" ++ show (head arguments)) $ return ()
  if localEff then do
    let [varAddr@(BindingAddr _ varName), _] = arguments
    unwindLookup varName knext mkaddr u ctx
  else do
    apply knext mkaddr (head arguments) ctx
doHandlerPrimitive name n addr knext mkaddr arguments venv ctx u | n == nameLocalSet = do
  let [varAddr@(BindingAddr _ varName), val] = arguments
  -- trace ("LocalSet: " ++ show name ++ " " ++ show n ++ "\n" ++ show args ++ "\n" ++ show arguments) $ return ()
  if localEff then do
    unwindSet varName val knext mkaddr addr u ctx
  else do
    rebind val varAddr 
    extendStore addr changeUnit
    apply knext mkaddr addr ctx
doHandlerPrimitive name n addr knext mkaddr arguments venv ctx u | n == nameHandle = do
  args <- mapM store arguments
  case args of 
    [AChangeObj _ _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] -> do
      let label = case exprOfCtx u of
            App (TypeApp _ [_, _, _, h, _]) _ _ -> labelName h
      k <- kLimit
      henv <- mEnvOf hnd
      -- trace ("OPS " ++ show henv) $ return ()
      let newctx = take k $ CallApp (contextId u) : ctx
      bod <- focusBody body
      -- MKHandle { eff :: Name, mkKNext:: Addr, mknext:: Addr, hnd :: ExprContext, henv :: VEnv, mkCtx:: CombinedCtx }
      let kmkaddr = ImplicitAddr ctx venv (contextId bod)
      extendKStore kmkaddr (KNext (FDollar (arguments !! 2) (contextId u)) EndKAddr)
      extendMKStore kmkaddr (MKHandle label knext mkaddr (Handler (arguments !! 1) (Just ret)) (M.unions [retenv, henv]))
      -- trace ("Applying handle: " ++ show label ++ " with env " ++ show venv) $ return ()
      eval bod (limitEnv bodyenv (fvs body)) kmkaddr kmkaddr newctx
    _ -> doBottom
doHandlerPrimitive name n addr knext mkaddr arguments venv ctx u | n == nameLocalVar = do
  -- trace ("LocalVar: " ++ show name ++ " " ++ show n) $ return ()
  args <- mapM store arguments
  if localEff then do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        let newEnv = M.insert varName ctx env
        bod <- focusBody e
        extendStore (fromJust $ lookupEnv varName newEnv) (head args)
        k <- kLimit
        let newctx = take k $ CallApp (contextId u): ctx
        let mk' = ImplicitAddr newctx venv (contextId u)
        extendMKStore mk' (MKHandle (getName varName) knext mkaddr (Handler (arguments !! 1) Nothing) newEnv)
        eval bod newEnv EndKAddr mk' newctx
  else do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        let newEnv = M.insert varName ctx env
        bod <- focusBody e
        extendStore (fromJust $ lookupEnv varName newEnv) (head args)
        eval bod newEnv knext mkaddr ctx
localEff = True

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

