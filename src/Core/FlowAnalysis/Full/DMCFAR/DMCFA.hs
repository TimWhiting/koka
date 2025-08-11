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
        -- trace ("Value not found in store :" ++ show addr)
        error ("Value not found in store: " ++ show addr)
        doBottom
      KStore addr -> if addr == EndKAddr then return $ KV KEnd else doBottom
      MKStore addr -> if addr == EndMKAddr then return $ MKV MKEnd else doBottom
      Step (CEval expr kaddr mkaddr ctx) -> do
        drive $ doEval expr kaddr mkaddr ctx
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

store :: HasCallStack => Addr -> FixAAMR r s e AChange
store addr = do
  SV res <- doStep (VStore addr)
  return res
kStore addr = do
  KV res <- doStep (KStore addr)
  return res
mkStore addr = do
  MKV res <- doStep (MKStore addr)
  return res
eval expr kaddr mkaddr ctx = return $ N (CEval expr kaddr mkaddr ctx)
apply kaddr mkaddr addr ctx = return $ N (CApply kaddr mkaddr addr ctx)
unwind name opName perform kaddr mkaddr addrs ctx = return $ N (CUnwind name opName perform kaddr mkaddr addrs ctx)

allocConst :: CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst ctx expr v = do
  let addr = BindImplicitAddr ctx (contextId expr)
  extendStore addr v
  return addr

allocFrame frame kaddr ctx u = do
  let addr = ImplicitAddr ctx u
  extendKStore addr (KNext frame ctx kaddr)
  return addr

fvsl :: [ExprContext] -> S.Set TName
fvsl exprs = S.unions $ map fvs exprs

primitiveFuncWrappers = [nameUnsafeNoLocalCast, nameUnsafeTotalCast]

doEval :: HasCallStack => ExprContext -> Addr -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
doEval expr kaddr mkaddr ctx =
  let open = case exprOfCtx expr of
        App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen -> True
        _ -> False 
      process x = if not open then do 
                    -- analysisLog ("Evaluating: " ++ showCtxExpr expr ++ " in " ++ show ctx) 
                    x
                  else x 
  in 
  process $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
  case exprOfCtx expr of
    App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      eval f kaddr mkaddr ctx
    App (TypeApp (Var name _) _) [_,_,f] _ | getName name == nameMaskAt -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 3 expr
      -- trace ("Masking " ++ show f) $ return ()
      k' <- addFrame FMask (contextId f)
      eval f k' mkaddr ctx
    App (TypeApp (Var name _) _) [f] _ | getName name == nameMaskBuiltin -> do
      -- TODO: Adjust the dynamic context to only what is necessary
      f <- focusChild 1 expr
      -- trace ("Masking " ++ show f) $ return ()
      k' <- addFrame FMask (contextId f)
      eval f k' mkaddr ctx
    Con tn _ _ -> do
      let params = case splitFunScheme (typeOf tn) of
                      Just (_, params, _, _) -> map fst params
                      Nothing -> []
      -- trace ("Con: " ++ show tn ++ " with params: " ++ show params) $ return ()
      let constr = AChangeConstr expr params
      addr <- allocConst ctx expr constr
      apply kaddr mkaddr addr (dynamic ctx)
    Var name _ -> do
      if isPrimitive name then do
        addr <- allocConst ctx expr (AChangePrim name expr)
        apply kaddr mkaddr addr (dynamic ctx)
      else if qualifier (getName name) == nameCoreHnd then
        error ("Unexpected handler library name in DMCFA: " ++ show name)
      else if qualifier (getName name) == nameNil then do
        -- trace ("Found variable: " ++ show name ++ " at " ++ show name) $ return ()
        apply kaddr mkaddr (BindingAddr ctx name) (dynamic ctx)
      else do
        res <- bindExternal name
        case res of -- TODO: Evaluate top bindings and store them somewhere, don't re-evaluate based on kaddrs
          Just expr -> do
            -- trace ("Evaluating external: " ++ show name) $ return ()
            extendMKStore (TopAddr name) MKEnd
            c <- startCombinedCtx
            each [eval expr EndKAddr (TopAddr name) c,
                  apply kaddr mkaddr (BindingAddr c name) (dynamic ctx)]
          Nothing -> do
            -- trace ("Found variable: " ++ show name ++ " at " ++ show name) $ return ()
            apply kaddr mkaddr (BindingAddr ctx name) (dynamic ctx)
    Lit l -> do
      addr <- allocConst ctx expr (injLit l)
      apply kaddr mkaddr addr (dynamic ctx)
    Lam{} -> do
      addr <- allocConst ctx expr (AChangeClos expr ctx)
      apply kaddr mkaddr addr (dynamic ctx)
    App _ args _ -> doApp args
    Let dgs _ -> do
      child <- childrenContexts expr
      -- trace ("LetChildren: " ++ intercalate "\n" (map show child)) $ return ()
      bind <- focusLetDefBinding 0 0 expr
      let defGroup = head dgs
      -- let newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) venv (defsOf defGroup)
      let defName = defTName (defOfCtx bind)
      -- trace ("Let binding: " ++ show defName ++ " in " ++ show ctx) $ return ()
      k' <- addFrame (FLet 0 (length dgs) 0 (length (defsOf defGroup)) defName [] expr) (contextId bind)
      eval bind k' mkaddr ctx
    -- TODO: Let and case
    TypeApp{} -> do
      e <- focusChild 0 expr
      eval e kaddr mkaddr ctx
    TypeLam _ Lam{} -> do
      addr <- allocConst ctx expr (AChangeClos expr ctx)
      apply kaddr mkaddr addr (dynamic ctx)
    TypeLam _ (App _ args _) -> doApp args
    TypeLam _ _ -> do --(TypeApp Var{} _)
      childs <- childrenContexts expr
      -- trace ("TypeLam: " ++ show (map contextId childs)) $ return ()
      e <- focusChild 0 expr
      eval e kaddr mkaddr ctx
    Case _ brs -> do
      s <- focusScrutinee expr
      branches <- mapM (\i -> focusBranch i expr) [0..length brs - 1]
      k' <- addFrame (FScrut expr branches) (contextId s)
      eval s k' mkaddr ctx
    -- TypeLam _ e -> do
    --   trace ("TypeLam not handled yet: " ++ show e) $ doBottom
  where addFrame f u = allocFrame f kaddr ctx u
        doApp args = do
          f <- focusFun expr
          argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
          k' <- addFrame (FApp (length args) argExprs [] expr) (contextId f)
          eval f k' mkaddr ctx

rebindAll :: HasCallStack => S.Set TName -> CombinedCtx -> CombinedCtx -> FixAAMR r s e ()
rebindAll fvs oldCtx newCtx = do
  if oldCtx == newCtx || S.null fvs then return ()
  else do
    -- trace ("Rebinding: " ++ show fvs ++ " from " ++ show oldCtx ++ " to " ++ show newCtx) $ return ()
    let bindings = S.toList fvs
    mapM_ (\tname -> do
      v <- store (BindingAddr oldCtx tname)
      extendStore (BindingAddr newCtx tname) v) bindings

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
          if mkaddr == EndMKAddr then do
            endV <- store addr
            extendStore EndVAddr endV
            return $ N CDone
          else do
            topV <- store addr
            let TopAddr tname = mkaddr
            -- trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
            -- let [(tname, ctx)] = M.toList env
            c <- startCombinedCtx
            extendStore (BindingAddr c tname) topV
            return $ N CDone
        MKHandle _ knext mknext _ dynctx ->
          apply knext mknext addr (dynamic dynctx)
    KNext frame ctx knext ->
      let newctx = CombinedCtx (kfvs ctx) (static ctx) dynctx
          addFrame f u = allocFrame f knext newctx u in
      case frame of
        f | f == FCall || f == FMask -> do
          v <- store addr
          case v of
            AChangeClos e env -> do
              bod <- focusBody e
              let nCtx = replaceFvs newctx (fvs e)
              rebindAll (kfvs ctx) ctx nCtx
              eval bod knext mkaddr nCtx
        FApp n args res u -> do
          case args of
            [] -> case res ++ [addr] of
              f:arguments -> do
                -- trace ("Applying: " ++ show args ++ " " ++ show (res ++ [addr])) $ return ()
                -- trace ("Real params: " ++ show params) $ return ()
                res <- store f
                -- trace ("Applying function: " ++ show f ++ " " ++ show res) $ return ()
                case res of
                  AChangeClos cexpr cctx -> do
                    body <- focusBody cexpr
                    let args = lamNames cexpr
                    m <- mLimit
                    let newCtx = CombinedCtx (fvs cexpr) (take m $ CallApp (contextId u) : static newctx) (dynamic newctx)
                    -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show args) $ return ()
                    zipWithM_ (\a p -> do
                      val <- store p
                      extendStore (BindingAddr newCtx a) val) args arguments
                    k' <- kStore knext
                    let ia = ImplicitAddr newCtx (contextId body)
                    extendKStore ia k'
                    rebindAll (fvs cexpr) cctx newCtx
                    eval body ia mkaddr newCtx
                  AChangePrim name pms -> do
                    args <- mapM store arguments
                    let addr = BindImplicitAddr newctx (contextId u)
                    let n = getName name
                    if isHandlerPrimitive n then
                      doHandlerPrimitive name n addr knext mkaddr arguments args ctx newctx u
                    else do
                      res <- doPrimitive n args
                      extendStore addr res
                      apply knext mkaddr addr dynctx
                  AChangeConstr con params -> do
                    let name = case exprOfCtx con of
                          Con n _ _ -> n
                          _ -> error "Expected a constructor"
                    let addr = BindImplicitAddr newctx (contextId u)
                    extendStore addr (AChangeObj name (zip params arguments))
                    apply knext mkaddr addr dynctx
                  AChangeKont label kx hctx hnd@(Handler _ _ hfvs) -> do
                    m <- mLimit
                    d <- dLimit
                    let newCtx = CombinedCtx (kfvs ctx) (take m $ CallApp (contextId u) : static newctx) (dynamic newctx)
                        newDynCtx = take d $ (contextId u, static newCtx):dynamic newctx
                        mk' = ImplicitAddr newCtx (contextId u)
                    rebindAll hfvs hctx newCtx
                    extendMKStore mk' (MKHandle label knext mkaddr hnd newCtx)
                    apply kx mk' addr newDynCtx
                  _ -> do
                    trace ("Applying non function: " ++ show res) doBottom
            next:rest -> do
              k' <- addFrame (FApp n rest (res ++ [addr]) u) (contextId next)
              rebindAll (kfvs ctx) ctx newctx
              eval next k' mkaddr newctx
        FLet groupIdx numGroups bindingIdx numBindings name resolved u -> do
          -- trace "Applying Let" $ return ()
          val <- store addr
          -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show newctx ) $ return ()
          extendStore (BindingAddr newctx name) val
          let newFvs = S.insert name (kfvs ctx)
          let newCtx = replaceFvs newctx newFvs
          -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
          if isLetDefBindingFinished groupIdx bindingIdx u then do
            body <- focusLetBod u
            rebindAll (kfvs ctx) ctx newCtx
            eval body knext mkaddr newctx
          else do
            next <- focusLetDefBinding groupIdx bindingIdx u
            k' <- addFrame (nextLetFrame frame newctx) (contextId next)
            let allNextFvs = letFvs groupIdx bindingIdx u
            rebindAll (kfvs ctx) ctx newCtx
            eval next k' mkaddr newCtx
        FScrut parent branches -> do
          let recur [] = doBottom
              recur ((branch, expr):branches) = do
                match <- branchMatch branch addr
                case match of
                  Just bindings -> do
                    mapM_ (\(tname, extend) ->
                      extend (BindingAddr newctx tname)
                      ) (M.toList bindings)
                    rebindAll (kfvs ctx) ctx newctx
                    eval expr knext mkaddr newctx
                  Nothing -> recur branches
          case exprOfCtx parent of
            Case _ pats -> recur (zip pats branches)
        FHLink eff perform k' h -> do
          let ia = ImplicitAddr newctx perform
          extendMKStore ia (MKHandle eff knext mkaddr h newctx)
          apply k' ia addr dynctx
        _ -> trace ("Applying unknown frame: " ++ show frame) doBottom

doUnwind :: HasCallStack => Name -> Name -> ExprContext -> Addr -> Addr -> [Addr] -> CombinedCtx -> FixAAMR r s e FixChange
doUnwind name opName performExpr kaddr mkaddr args ctx = do
  mk <- mkStore mkaddr
  case mk of
    MKEnd -> doBottom -- error ("Unwind: No MKont found for " ++ show name ++ " " ++ show performExpr)
    MKHandle eff mkKNext mknext h@(Handler hnd ret hfvs) mkCtx -> do
      if eff == name then do
        AChangeObj tname hndargs@(_:ops) <- store hnd
        hargs <- mapM (store . snd) hndargs
        -- trace ("Unwinding: " ++ show (map fst ops) ++ " " ++ show opName ++ " " ++ show hargs) $ return ()
        let unmakeHidden ('-':rest) = newName rest
            unmakeHidden (_:rest) = unmakeHidden rest
        let ops' = map (\(n, a) -> (unmakeHidden $ nameStem n, a)) ops
        case lookup opName ops' of
          Nothing ->
            -- trace ("Unwind: Operation " ++ show opName ++ " not found in " ++ show ops')
            doBottom
          Just op -> do
            o <- store op
            -- trace ("Unwinding operation: " ++ show opName ++ " with " ++ show o) $ return ()
            AChangeObj _ [opAddr] <- store op
            AChangeClos op openv <- store (snd opAddr)
            let params = lamNames op
            bod <- focusBody op
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (BindingAddr mkCtx) params)
            extendStore (BindingAddr mkCtx (last params)) (AChangeKont name kaddr mkCtx h)
            eval bod mkKNext mknext mkCtx
      else do
        let k' = ImplicitLAddr ctx (contextId performExpr)
        extendKStore k' (KNext (FHLink eff (contextId performExpr) kaddr h) ctx mkKNext)
        unwind name opName performExpr k' mknext args mkCtx


unwindLookup :: HasCallStack => TName -> Addr -> Addr -> ExprContext -> FixAAMR r s e FixChange
unwindLookup varName knext mkaddr u = do
  mk <- mkStore mkaddr
  case mk of
    MKHandle nm k' mknext h ctx | getName varName == nm -> do
      apply knext mkaddr (BindingAddr ctx varName) (dynamic ctx)
    MKHandle nm k' mknext h ctx -> do
      let kx = ImplicitLAddr ctx (contextId u)
      extendKStore kx (KNext (FHLink nm (contextId u) knext h) ctx k')
      unwindLookup varName kx mknext u

unwindSet :: HasCallStack => TName -> AChange -> Addr -> Addr -> Addr -> ExprContext -> FixAAMR r s e FixChange
unwindSet varName val knext mkaddr addr u = do
  mk <- mkStore mkaddr
  case mk of
    MKHandle nm k' mknext h ctx | getName varName == nm -> do
      d <- dLimit
      m <- mLimit
      let newctx = CombinedCtx (kfvs ctx) (take m [CallDelim]) (take d $ (contextId u, static ctx):dynamic ctx)
      extendStore (BindingAddr newctx varName) val
      let mk' = ImplicitAddr newctx (contextId u)
      extendMKStore mk' (MKHandle nm k' mknext h newctx)
      extendStore addr changeUnit
      apply knext mk' addr (dynamic newctx)
    MKHandle nm k' mknext h ctx -> do
      let kx = ImplicitLAddr ctx (contextId u)
      extendKStore kx (KNext (FHLink nm (contextId u) knext h) ctx k')
      unwindSet varName val kx mknext addr u

isHandlerPrimitive :: Name -> Bool
isHandlerPrimitive n =
  n == nameHandle || isClauseName n || n == nameHTag
  || n == nameEvvAt || n == nameMaskAt || isNamePerform n || isClauseName n
  || n == nameLocalVar || n == nameLocalGet || n == nameLocalSet

fvsVal :: AChange ->FixAAMR r s e (S.Set TName)
fvsVal (AChangeClos e _) = return $ fvs e
fvsVal (AChangeObj _ args) = do
  args' <- mapM (store . snd) args
  fvss <- mapM fvsVal args'
  return $ S.unions fvss
fvsVal _ = return S.empty

doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> Addr -> Addr -> [Addr] -> [AChange] -> CombinedCtx -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
  extendStore addr (AChangeObj name (zip (repeat nameNil) arguments))
  apply knext mkaddr addr (dynamic ctx)
doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | isNamePerform n = do
  let label = case exprOfCtx u of
        App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 1))
        _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
  let AChangeClos select senv = args !! 1
  let DefCNonRec _ _ opName = select
  let opN = newName $ nameLocalQual (getName opName)
  -- trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
  doUnwind label opN u knext mkaddr (drop 2 arguments) ctx
doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | n == nameLocalGet = do
  -- trace ("LocalGet: " ++ show name ++ " " ++ show n ++ "\n" ++ show (head arguments)) $ return ()
  if localEff then do
    let [varAddr@(BindingAddr ctx varName), _] = arguments
    unwindLookup varName knext mkaddr u
  else do
    apply knext mkaddr (head arguments) (dynamic ctx)
doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | n == nameLocalSet = do
  let [_, val] = args
  let [varAddr@(BindingAddr ctx varName), _] = arguments
  -- trace ("LocalSet: " ++ show name ++ " " ++ show n ++ "\n" ++ show args ++ "\n" ++ show arguments) $ return ()
  if localEff then do
    unwindSet varName val knext mkaddr addr u
  else do
    extendStore varAddr val
    extendStore addr changeUnit
    apply knext mkaddr addr (dynamic ctx)
doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | n == nameHandle = do
  args <- mapM store arguments
  let [AChangeObj _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] = args
  let label = case exprOfCtx u of
        App (TypeApp _ [_, _, _, h, _]) _ _ -> labelName h
  d <- dLimit
  m <- mLimit
  -- trace ("OPS " ++ show ctx) $ return ()
  let newctx = CombinedCtx (kfvs ctx) (take m [CallDelim]) (take d $ (contextId u, static ctx):dynamic ctx)
  bod <- focusBody body
  let mk' = ImplicitAddr newctx (contextId u)
  rebindAll (kfvs ctxOld) ctxOld newctx
  extendMKStore mk' (MKHandle label knext mkaddr (Handler (arguments !! 1) (Just ret) (kfvs ctxOld)) newctx)
  -- trace ("Applying handle: " ++ show label ++ " with env " ++ show newctx) $ return ()
  eval bod EndKAddr mk' newctx
doHandlerPrimitive name n addr knext mkaddr arguments args ctxOld ctx u | n == nameLocalVar = do
  -- trace ("LocalVar: " ++ show name ++ " " ++ show n) $ return ()
  if localEff then do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        let newEnv = M.insert varName ctx
        bod <- focusBody e
        extendStore (BindingAddr ctx varName) (head args)
        d <- dLimit
        m <- mLimit
        let newctx = CombinedCtx (kfvs ctx) (take m [CallDelim]) (take d $ (contextId u, static ctx):dynamic ctx)
        let mk' = ImplicitAddr newctx (contextId u)
        extendMKStore mk' (MKHandle (getName varName) knext mkaddr (Handler (arguments !! 1) Nothing (S.singleton varName)) newctx)
        eval bod EndKAddr mk' newctx
  else do
    case args !! 1 of
      AChangeClos e env -> do
        let varName = head (lamNames e)
        bod <- focusBody e
        extendStore (BindingAddr ctx varName) (head args)
        eval bod knext mkaddr ctx
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

