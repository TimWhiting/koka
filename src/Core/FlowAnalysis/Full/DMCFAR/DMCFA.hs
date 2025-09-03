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
import qualified Core.FlowAnalysis.StaticContext as SC
import GHC.Stack (prettyCallStack, callStack)

nextAndFvs e = S.union (fvvs e) (SC.nextFvs e)

drive :: FixAAMR r s e FixChange -> FixAAMR r s e FixChange
drive m = do
  N res <- m
  each [
    return $ N res,
    do
      doStep (Step res)
      doBottom]

evalRes :: FixAAMR r s e FixChange -> FixAAMR r s e () 
evalRes m = do
  N res <- m
  case res of 
    CDone -> return ()
    c -> evalRes $ doStep (Step c)

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
      Step (CUnwindLookup varName knext mkaddr mkaddrX dynctx u) -> do
        drive $ unwindLookup varName knext mkaddr mkaddrX dynctx u
      Step (CUnwindSet varName val knext mkaddr addr ctx u) -> do
        drive $ unwindSet varName val knext mkaddr addr ctx u
      Step CDone -> return $ N CDone

extendStore :: HasCallStack => Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  -- trace ("Extending store: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (VStore addr) (SV v)
extendKStore :: Addr -> Kont -> FixAAMR r e s ()
extendKStore addr v = do
  -- trace ("Extending KStore: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (KStore addr) (KV v)
extendMKStore :: Addr -> MKont -> FixAAMR r e s ()
extendMKStore addr v = do
  -- case v of 
  --   MKHandle{} ->
  --     trace ("Extending MKStore: " ++ show addr ++ " with " ++ show v) $ return ()
  --   _ -> return ()
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
unwind_lookup varName knext mkaddr mkaddrX dynctx u = return $ N (CUnwindLookup varName knext mkaddr mkaddrX dynctx u)
unwind_set varName val knext mkaddr addr ctx u = return $ N (CUnwindSet varName val knext mkaddr addr ctx u)

allocConst :: CombinedCtx -> ExprContext -> AChange -> FixAAMR r s e Addr
allocConst ctx expr v = do
  let addr = BindImplicitAddr ctx (contextId expr)
  extendStore addr v
  return addr

allocFrame frame kaddr ctx u = do
  let addr = ImplicitAddr ctx u
  extendKStore addr (KNext frame ctx kaddr)
  return addr

primitiveFuncWrappers = [nameUnsafeNoLocalCast, nameUnsafeTotalCast]

doEval :: HasCallStack => ExprContext -> Addr -> Addr -> CombinedCtx -> FixAAMR r s e FixChange
doEval expr kaddr mkaddr ctx =
  let open = case exprOfCtx expr of
        App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen -> True
        _ -> False
      process x = if not open then do
                    -- analysisLog ("Evaluating: " ++ showCtxExpr expr ++ " " ++ show (contextId expr) ++ ":" ++ show ctx)
                    x
                  else x
  in
  process $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
  case exprOfCtx expr of
    App (TypeApp (Var name _) _) [arg] _ | getName name == nameEffectOpen || getName name == namePretendDecreasing -> do
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
            each [
                eval expr EndKAddr (TopAddr name) c,
                apply kaddr mkaddr (TopAddr name) (dynamic ctx)
              ]
            -- evalRes (eval expr (BEnv S.empty) EndKAddr (TopAddr name) c)
            -- apply kaddr mkaddr (TopAddr name) (dynamic ctx)
          Nothing -> do
            -- trace ("Found variable: " ++ show name ++ " at " ++ show name) $ return ()
            apply kaddr mkaddr (BindingAddr ctx name) (dynamic ctx)
    Lit l -> do
      addr <- allocConst ctx expr (injLit (contextId expr) l)
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
    -- trace ("Rebinding: " ++ show fvs ++ " from " ++ show oldCtx ++ " to " ++ show newCtx ++ "\n" ++ prettyCallStack callStack) $ return ()
    let bindings = S.toList fvs
    mapM_ (\tname -> do
      v <- store (BindingAddr oldCtx tname)
      extendStore (BindingAddr newCtx tname) v) bindings

doApply :: HasCallStack => Addr -> Addr -> Addr -> DynamicCtx -> FixAAMR r s e FixChange
doApply kaddr mkaddr addr dynctx = do
  k <- kStore kaddr
  -- trace ("Applying: " ++ show addr ++ " with " ++ show kaddr ++ " " ++ show mkaddr ++ ":" ++ show dynctx ++ "\n" ++ show k ) $ return ()
  -- trace ("Applying: " ++ show k) $ return ()
  case k of
    KEnd -> do
      mk <- mkStore mkaddr
      case mk of
        MKEnd -> do
          if mkaddr == EndMKAddr then do
            endV <- store addr
            -- trace ("Done! " ++ show mkaddr) $ return ()
            extendStore EndVAddr endV
            return $ N CDone
          else do
            topV <- store addr
            let TopAddr tname = mkaddr
            -- trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
            -- let [(tname, ctx)] = M.toList env
            c <- startCombinedCtx
            extendStore (TopAddr tname) topV
            return $ N CDone
        MKHandle _ knext mknext _ dynctx -> 
          apply knext mknext addr (dynamic dynctx) -- Happens for variables
    KNext frame ctx knext ->
      let newctx = CombinedCtx (static ctx) dynctx
          addFrame f u = allocFrame f knext newctx u in
      -- trace ("Applying " ++ show frame) $ 
      case frame of
        f | f == FCall || f == FMask -> do
          v <- store addr
          case v of
            AChangeClos e cctx -> do
              bod <- focusBody e
              let env' = BEnv $ fvvs e
              -- trace ("FMask " ++ show env' ++ " ctx " ++ show ctx ++ " cctx " ++ show cctx ++ " newctx " ++ show newctx) $ return ()
              rebindAll (bvars env') cctx newctx
              eval bod knext mkaddr newctx
        FDollar va -> do
          mk <- mkStore mkaddr
          case mk of
            MKEnd -> doBottom
            MKHandle _ knext mknext h@(Handler _ _) dynctx -> do
              res <- store va
              case res of
                AChangeClos cexpr cctx -> do
                  body <- focusBody cexpr
                  let [arg] = lamNames cexpr
                  m <- mLimit
                  -- trace ("Applying closure: " ++ show cexpr ++ " with " ++ show args) $ return ()
                  v <- store addr
                  -- rebindAll (fvs cexpr) cctx dynctx
                  -- rebindAll (bvars henv) ctx dynctx
                  extendStore (BindingAddr dynctx arg) v
                  eval body knext mknext dynctx
        FResume label kont hnd u -> do
          m <- mLimit
          d <- dLimit
          let newCtx = addCall m newctx u
              newDynCtx = addDelim d newCtx u
              mk' = ImplicitAddr newCtx u
          -- trace ("Applying resume continuation " ++ show u ++ " " ++ show label ) $ return () -- ++ "for\n" ++ 
          extendMKStore mk' (MKHandle label knext mkaddr hnd newCtx)
          apply kont mk' addr newDynCtx
        FApp n args res u -> do
          case args of
            [] -> case res ++ [addr] of
              f:arguments -> do
                -- trace ("Applying: " ++ show args ++ " " ++ show (res ++ [addr])) $ return ()
                res <- store f
                -- trace ("Applying function: " ++ show f ++ " " ++ show res) $ return ()
                case res of
                  AChangeClos cexpr cctx -> do
                    body <- focusBody cexpr
                    let args = lamNames cexpr
                    m <- mLimit
                    let newCtx = addCall m newctx (contextId u)
                    -- trace ("Applying closure: " ++ show cexpr ++ ":" ++ show newCtx ++ " fvvs: " ++ show (fvvs cexpr) ++ " args " ++ show args) $ return ()
                    zipWithM_ (\a p -> do
                      val <- store p
                      -- trace (show val ++ " from " ++ show p ++ " rebinding to " ++ show (BindingAddr newCtx a)) $ return ()
                      extendStore (BindingAddr newCtx a) val) args arguments
                    k' <- kStore knext
                    let ia = ImplicitAddr newCtx (contextId body)
                    extendKStore ia k'
                    -- trace ("Rebinding for closure " ++ show (fvvs cexpr) ++ " <-> " ++ show (fvvs cexpr) ++ " ctx " ++ show cctx ++ " " ++ show newCtx) $ return ()
                    rebindAll (fvvs cexpr) cctx newCtx
                    eval body ia mkaddr newCtx
                  AChangePrim name pms -> do
                    let addr = BindImplicitAddr newctx (contextId u)
                    let n = getName name
                    -- trace ("Applying primitive " ++ show name) $ return ()
                    -- rebindAll (bvars env) ctx newctx
                    if isHandlerPrimitive n then
                      doHandlerPrimitive name n addr knext mkaddr arguments newctx u
                    else do
                      args <- mapM store arguments
                      res <- doPrimitive n args
                      extendStore addr res
                      apply knext mkaddr addr dynctx
                  AChangeConstr con params -> do
                    let name = case exprOfCtx con of
                          Con n _ _ -> n
                          _ -> error "Expected a constructor"
                    let addr = BindImplicitAddr newctx (contextId u)
                    let conParams = map (\nm -> ConImplicitAddr nm newctx (contextId u)) params
                    zipWithM_ rebind arguments conParams
                    extendStore addr (AChangeObj con name (zip params conParams))
                    apply knext mkaddr addr dynctx
                  AChangeKont label kx hctx hnd@(Handler _ _) -> do
                    m <- mLimit
                    d <- dLimit
                    let newCtx = addCall m newctx (contextId u)
                        newDynCtx = addDelim d newCtx (contextId u)
                        -- newHEnv = nextFvs u
                        mk' = ImplicitAddr newCtx (contextId u)
                    -- trace ("Applying continuation " ++ show (contextId u) ++ " rebinding " ++ show newHEnv ) $ return () -- ++ "for\n" ++ 
                    --        show res ++ "\n" ++ show kaddr ++ "\n" ++ show mkaddr ++ "\n" ++ show addr ++ "\n" ++ show dynctx) $ return ()
                    extendMKStore mk' (MKHandle label knext mkaddr hnd newCtx)
                    apply kx mk' addr newDynCtx
                  _ -> do
                    trace ("Applying non function: " ++ show res) doBottom
            next:rest -> do
              k' <- addFrame (FApp n rest (res ++ [addr]) u) (contextId next)
              let vars = nextAndFvs next
              rebindAll vars ctx newctx
              eval next k' mkaddr newctx
        FLet groupIdx numGroups bindingIdx numBindings name resolved u -> do
          -- trace ("Applying Let " ++ show env) $ return ()
          val <- store addr
          extendStore (BindingAddr newctx name) val
          -- trace (show u ++ " has free vars " ++ show env') $ return ()
          -- trace ("Binding " ++ show name ++ " to " ++ show val ++ " in " ++ show newctx ++ " old: " ++ show ctx ) $ return ()
          -- trace ("Applying Let: " ++ show groupIdx ++ " " ++ show bindingIdx) $ return ()
          if isLetDefBindingFinished groupIdx bindingIdx u then do
            body <- focusLetBod u
            rebindAll (S.delete name $ fvvs body) ctx newctx
            eval body knext mkaddr newctx
          else do
            next <- focusNextLetDefBinding groupIdx bindingIdx u
            rebindAll (S.delete name (nextFvs next)) ctx newctx
            k' <- addFrame (nextLetFrame frame newctx) (contextId next)
            eval next k' mkaddr newctx
        FScrut parent branches -> do
          let recur [] = doBottom
              recur ((branch, expr):branches) = do
                match <- branchMatch branch addr
                case match of
                  Just bindings -> do
                    mapM_ (\(tname, extend) ->
                      extend (BindingAddr newctx tname)
                      ) (M.toList bindings)
                    rebindAll (S.union (fvvs expr) (nextFvs expr)) ctx newctx
                    eval expr knext mkaddr newctx
                  Nothing -> recur branches
          case exprOfCtx parent of
            Case _ pats -> recur (zip pats branches)
        FHLink eff perform hctx k' h -> do
          -- trace ("Link restore " ++ show kaddr ++ " " ++ show newctx ++ "\n" ++ show ctx ++ "\n" ++ show hctx) $ return ()
          let ia = ImplicitLRAddr newctx eff perform
          d <- dLimit
          extendMKStore ia (MKHandle eff knext mkaddr h newctx)
          let newDCtx = take d ((hctx, static ctx): dynctx)
          apply k' ia addr newDCtx
        _ -> trace ("Applying unknown frame: " ++ show frame) doBottom

doUnwind :: HasCallStack => Name -> Name -> ExprContext -> Addr -> Addr -> [Addr] -> CombinedCtx -> FixAAMR r s e FixChange
doUnwind name opName performExpr kaddr mkaddr args ctx = do
  mk <- mkStore mkaddr
  case mk of
    MKEnd -> doBottom -- error ("Unwind: No MKont found for " ++ show name ++ " " ++ show performExpr)
    MKHandle eff mkKNext mknext h@(Handler hnd ret) mkCtx -> do
      if eff == name then do
        m <- mLimit
        -- let newCtx = mkCtx -- addCall m mkCtx (contextId performExpr)
        -- trace ("Matched " ++ show mkCtx) $ return ()
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
            -- trace ("Unwinding operation: " ++ show opName ++ " with " ++ show o) $ return ()
            AChangeObj _ opConName [opAddr] <- store op
            AChangeClos op opCtx <- store (snd opAddr)
            let params = lamNames op
            bod <- focusBody op
            rebindAll (fvvs op) opCtx mkCtx
            -- let opCtx = mkCtx -- {kfvs = S.union (S.fromList params) (kfvs mkCtx)}
            -- trace ("Params: " ++ show (length args) ++ " " ++ show (length params)) $ return ()
            zipWithM_ rebind args (map (BindingAddr mkCtx) params)
            -- rebindAll (S.difference (bvars henv) (S.fromList params)) lastCtx mkCtx
            if nameStem (getName opConName) `startsWith` "clause-tail" then do
              let k' = ImplicitAddr mkCtx (contextId bod)
              extendKStore k' (KNext (FResume eff kaddr h (contextId bod)) mkCtx mkKNext)
              eval bod k' mknext mkCtx
            else if nameStem (getName opConName) `startsWith` "clause-never" then do
              eval bod mkKNext mknext mkCtx
            else do
              extendStore (BindingAddr mkCtx (last params)) (AChangeKont name kaddr mkCtx h)
              eval bod mkKNext mknext mkCtx
      else do
        let k' = ImplicitLAddr ctx opName (contextId performExpr)
        -- trace ("Link create " ++ show k' ++ " " ++ show ctx ++ "\n" ++ show mkCtx) $ return ()
        extendKStore k' (KNext (FHLink eff (contextId performExpr) (ctxHnd ctx) kaddr h) mkCtx mkKNext)
        unwind name opName performExpr k' mknext args mkCtx


unwindLookup :: HasCallStack => TName -> Addr -> Addr -> Addr -> DynamicCtx -> ExprContext -> FixAAMR r s e FixChange
unwindLookup varName knext mkaddr mkaddrX dynctx u = do
  mk <- mkStore mkaddrX
  case mk of
    MKHandle nm k' mknext h@(Handler{ops = varAddr}) ctx | getName varName == nm -> do
      apply knext mkaddr varAddr dynctx 
    MKHandle nm k' mknext h@(Handler _ _) ctx -> do
      unwind_lookup varName knext mkaddr mknext dynctx u
    _ -> doBottom

unwindSet :: HasCallStack => TName -> Addr -> Addr -> Addr -> Addr -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
unwindSet varName val knext mkaddr addr ctx u = do
  mk <- mkStore mkaddr
  case mk of
    MKHandle nm k' mknext h mkCtx | getName varName == nm -> do
      d <- dLimit
      m <- mLimit
      v <- store val
      let u = vcontextId v
      let newctx = addCall m mkCtx u
      let newAddr = BindingAddr newctx varName
      rebind val newAddr
      -- rebindAll (S.delete varName (bvars (henv h))) mkCtx newctx
      let mk' = ImplicitAddr newctx u
      extendMKStore mk' (MKHandle nm k' mknext h{ops = newAddr} newctx)
      extendStore addr changeUnit
      let newDelimCtx = addDelim d newctx u
      -- trace ("Extended time " ++ show newDelimCtx) $ return ()
      apply knext mk' addr newDelimCtx
    MKHandle nm k' mknext h@(Handler _ _) mkCtx -> do
      let kx = ImplicitLAddr ctx (getName varName) (contextId u)
      extendKStore kx (KNext (FHLink nm (contextId u) (ctxHnd ctx) knext h) mkCtx k')
      unwind_set varName val kx mknext addr mkCtx u
    _ -> doBottom

isHandlerPrimitive :: Name -> Bool
isHandlerPrimitive n =
  n == nameHandle || isClauseName n || n == nameHTag
  || n == nameEvvAt || n == nameMaskAt || isNamePerform n 
  || n == nameLocalVar || n == nameLocalGet || n == nameLocalSet

fvsVal :: AChange -> FixAAMR r s e [(S.Set TName, CombinedCtx)]
fvsVal (AChangeClos e ctx) = return [(fvvs e, ctx)]
fvsVal (AChangeObj _ _ args) = do
  args' <- mapM (store . snd) args
  fvss <- mapM fvsVal args'
  return $ concat fvss
fvsVal _ = return []

doHandlerPrimitive :: HasCallStack => TName -> Name -> Addr -> Addr -> Addr -> [Addr] -> CombinedCtx -> ExprContext -> FixAAMR r s e FixChange
doHandlerPrimitive name n addr knext mkaddr arguments ctx u | isClauseName n || n == nameHTag || n == nameEvvAt = do
  let conParams = zipWith (\_ i -> ConImplicitAddr (newName $ nameStem n ++ show i) ctx (contextId u)) arguments [1..]
  zipWithM_ rebind arguments conParams
  extendStore addr (AChangeObj u name (zip (repeat nameNil) conParams))
  apply knext mkaddr addr (dynamic ctx)
doHandlerPrimitive name n addr knext mkaddr arguments ctx u | isNamePerform n = do
  args <- mapM store arguments
  let label = case exprOfCtx u of
        App (TypeApp _ tps) _ _ -> labelName (tps !! (length tps - 1))
        _ -> error $ "Expected a perform type application " ++ show (exprOfCtx u)
  let AChangeClos select senv = args !! 1
  let DefCNonRec _ _ opName = select
  let opN = newName $ nameLocalQual (getName opName)
  -- trace ("Performing: "  ++ show label ++ " " ++ show n ++ " with " ++ show select) $ return ()
  doUnwind label opN u knext mkaddr (drop 2 arguments) ctx
doHandlerPrimitive name n addr knext mkaddr arguments ctx u | n == nameLocalGet = do
  -- trace ("LocalGet: " ++ show name ++ " " ++ show n ++ "\n" ++ show (head arguments)) $ return ()
  if localEff then do
    let [varAddr@(BindingAddr _ varName), _] = arguments
    unwindLookup varName knext mkaddr mkaddr (dynamic ctx) u
  else do
    apply knext mkaddr (head arguments) (dynamic ctx)
doHandlerPrimitive name n addr knext mkaddr arguments ctx u | n == nameLocalSet = do
  let [varAddr@(BindingAddr _ varName), val] = arguments
  -- trace ("LocalSet: " ++ show name ++ " " ++ show n ++ "\n" ++ show arguments ++ "\n" ++ show arguments) $ return ()
  if localEff then do
    unwindSet varName val knext mkaddr addr ctx u
  else do
    rebind val varAddr
    extendStore addr changeUnit
    apply knext mkaddr addr (dynamic ctx)
doHandlerPrimitive name n addr knext mkaddr arguments ctx u | n == nameHandle = do
  args <- mapM store arguments
  case args of 
    [AChangeObj _ _ [hNameAddr], hnd, AChangeClos ret retenv, AChangeClos body bodyenv] -> do
      let label = case exprOfCtx u of
            App (TypeApp _ [_, _, _, h, _]) _ _ -> labelName h
      d <- dLimit
      m <- mLimit
      fvss <- fvsVal hnd
      bod <- focusBody body
      let bvars = fvvs body
      -- trace ("OPS " ++ show label ++ ":" ++ show ctx ++ " " ++ show (contextId u)) $ return ()
      let newctx = newDelim d m ctx (contextId u)
      let kmkaddr = ImplicitAddr newctx (contextId bod)
      extendKStore kmkaddr (KNext (FDollar (arguments !! 2)) newctx EndKAddr)
      extendMKStore kmkaddr (MKHandle label knext mkaddr (Handler (arguments !! 1) (Just ret)) ctx)
      --trace ("Applying handle: " ++ show label ++ " with env " ++ show newctx) $ return ()
      rebindAll bvars bodyenv newctx
      eval bod kmkaddr kmkaddr newctx
    _ -> doBottom
doHandlerPrimitive name n addr knext mkaddr arguments ctx u | n == nameLocalVar = do
  -- trace ("LocalVar " ++ show u) $ return ()
  args <- mapM store arguments
  if localEff then do
    case args !! 1 of
      AChangeClos e _ -> do
        let varName = head (lamNames e)
        bod <- focusBody e
        d <- dLimit
        m <- mLimit
        let newctx = newDelim d m ctx (contextId u)
        let mk' = ImplicitAddr newctx (contextId u)
        let varAddr = BindingAddr ctx varName
        extendStore varAddr (head args)
        rebindAll (fvvs bod) ctx newctx
        extendMKStore mk' (MKHandle (getName varName) knext mkaddr (Handler varAddr Nothing) ctx)
        eval bod EndKAddr mk' newctx
  else do
    case args !! 1 of
      AChangeClos e _ -> do
        let varName = head (lamNames e)
        bod <- focusBody e
        let env = BEnv (S.singleton varName)
        extendStore (BindingAddr ctx varName) (head args)
        eval bod knext mkaddr ctx
localEff = True

branchMatch :: Branch -> Addr -> FixAAMR r s e (Maybe (Bindings r s e))
branchMatch branch addr =
  patMatch (head $ branchPatterns branch) addr

type Bindings r s e = M.Map TName (Addr -> FixAAMR r s e ())

rebind :: HasCallStack => Addr -> Addr -> FixAAMR r s e ()
rebind oldAddr newAddr = do
  if oldAddr == newAddr then return ()
  else do 
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

