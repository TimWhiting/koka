{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
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
import Common.NamePrim (nameOpen, nameEffectOpen, nameHandle, namePerform, nameClause)
import Data.Maybe (fromJust)
import Compile.Module (Module(..))
import Common.Failure (HasCallStack)
import Type.Type (splitFunType, typeAny, splitFunScheme, Effect, typeTotal, effectExtend, extractEffectExtend)
import Control.Monad (foldM, zipWithM, zipWithM_)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)
import Type.Pretty (defaultEnv, ppType)
import Lib.PPrint (hcat, tupled, vcat, text)

mLimit :: Int
mLimit = 2

dLimit :: Int
dLimit = 2

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
      Step (CUnwind name n kaddr mkaddr addrs ctx) -> do
        drive $ doUnwind name n kaddr mkaddr addrs ctx
      Step CDone -> return $ N CDone

extendStore :: Addr -> AChange -> FixAAMR r e s ()
extendStore addr v = do
  trace ("Extending store: " ++ show addr ++ " with " ++ show v) $ return ()
  lift $ push (VStore addr) (SV v)
extendKStore :: Addr -> Kont -> FixAAMR r e s ()
extendKStore addr v = lift $ push (KStore addr) (KV v)
extendMKStore :: Addr -> MKont -> FixAAMR r e s ()
extendMKStore addr v= lift $ push (MKStore addr) (MKV v)

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
unwind name n kaddr mkaddr addrs ctx = return $ N (CUnwind name n kaddr mkaddr addrs ctx)

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
  trace ("Evaluating: " ++ show expr) $ --  ++ " " ++ show kaddr ++ " " ++ show ctx) $
  case exprOfCtx expr of
    App (TypeApp (Var name _) _) args _ | nameEffectOpen == getName name -> do
      f <- focusChild 1 expr
      eval f venv kaddr mkaddr ctx
    Con{} -> do
      let constr = AChangeConstr expr venv
      addr <- allocConst venv ctx expr constr
      apply kaddr mkaddr addr (dynamic ctx)
    Var name _ -> do
      if isPrimitive name then do
        addr <- allocConst venv ctx expr (AChangePrim name expr venv)
        apply kaddr mkaddr addr (dynamic ctx)
      else case lookupEnv name venv of
        Just addr -> apply kaddr mkaddr addr (dynamic ctx)
        Nothing -> do
          res <- bindExternal name
          case res of -- TODO: Evaluate top bindings and store them somewhere, don't re-evaluate based on kaddrs
            Just expr -> do
              trace ("Evaluating external: " ++ show name) $ return ()
              extendMKStore (endTopMKAddr name) MKEnd
              each [eval expr M.empty endKAddr (endTopMKAddr name) startCombinedCtx,
                    apply kaddr mkaddr (BindingAddr startCombinedCtx name) (dynamic ctx)]
            Nothing -> do
              trace ("Variable not found: " ++ show name) $ doBottom
    Lit l -> do
      addr <- allocConst venv ctx expr (injLit l)
      apply kaddr mkaddr addr (dynamic ctx)
    Lam{} -> do
      addr <- allocConst venv ctx expr (AChangeClos expr venv)
      trace ("Allocating closure: " ++ show addr ++ " " ++ show (dynamic ctx)) $ return ()
      apply kaddr mkaddr addr (dynamic ctx)
    App _ args _ -> do
      f <- focusFun expr
      argExprs <- zipWithM (\i _ -> focusParam i expr) [0..] args
      k' <- addFrame (FApp (length args) argExprs [] expr venv) (contextId f)
      eval f (limitEnv venv (fvs f)) k' mkaddr ctx
    Let dgs _ -> do
      trace ("Let: " ++ show (length dgs)) $ return ()
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
    TypeLam{} -> do
      e <- focusChild 0 expr
      eval e venv kaddr mkaddr ctx
    Case scrutinee branches -> do
      trace ("Case: " ++ show scrutinee) $ doBottom
  where addFrame f u = allocFrame f kaddr ctx venv u

doApply :: HasCallStack => Addr -> Addr -> Addr -> DynamicCtx -> FixAAMR r s e FixChange
doApply kaddr mkaddr addr dynctx = do
  k <- kStore kaddr
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
            trace ("Applying top value: " ++ show addr) $ return ()
            topV <- store addr
            let ImplicitAddr _ env _  = mkaddr
            trace ("Applying top value: " ++ show addr ++ " with " ++ show topV) $ return ()
            let [(tname, ctx)] = M.toList env
            extendStore (BindingAddr ctx tname) topV
            return $ N CDone
        MKHandle{} ->
          trace ("Apply MKHandle not handled yet: " ++ show mk) $
          doBottom
    KNext frame ctx knext ->
      let newctx = CombinedCtx ctx dynctx
          addFrame f venv u = allocFrame f knext newctx venv u in
      case frame of
        FApp n args res u venv -> do
          trace ("Applying: " ++ show args ++ " " ++ show (res ++ [addr])) $ return ()
          case args of
            [] -> case res ++ [addr] of
              f:params -> do
                -- trace ("Real params: " ++ show params) $ return ()
                -- trace ("Applying function: " ++ show f) $ return ()
                res <- store f
                case res of
                  AChangeClos cexpr cenv -> do
                    body <- focusBody cexpr
                    let args = lamNames cexpr
                    let newCtx = CombinedCtx (CallApp (contextId u) : static newctx) (dynamic newctx)
                    let newEnv = foldl (\acc x -> M.insert x newCtx acc) cenv args
                    zipWithM_ (\a p -> do
                      val <- store p
                      extendStore (fromJust $ lookupEnv a newEnv) val) args params
                    eval body (limitEnv newEnv (fvs body)) knext mkaddr newCtx
                  AChangePrim name _ venv -> do
                    args <- mapM store params
                    res <- doPrimitive (getName name) args venv
                    let addr = BindImplicitAddr newctx venv (contextId u)
                    extendStore addr res
                    apply knext mkaddr addr dynctx
                  AChangeConstr con _ -> do 
                    let name = case exprOfCtx con of 
                          Con n _ _ -> n
                          _ -> error "Expected a constructor"
                    let addr = BindImplicitAddr newctx venv (contextId u)
                    extendStore addr (AChangeObj name params)
                    apply knext mkaddr addr dynctx
                  _ -> do
                    trace ("Applying non function: " ++ show res) $ doBottom
            next:rest -> do
              k' <- addFrame (FApp n rest (res ++ [addr]) u (limitEnv venv (fvsl rest))) venv (contextId next)
              eval next (limitEnv venv (fvs next)) k' mkaddr newctx
        FLet groupIdx numGroups bindingIdx numBindings name resolved u venv -> do
          val <- store addr
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
        _ ->
          trace ("Apply not handled yet" ++ show k) $ doBottom

doUnwind :: HasCallStack => Name -> Int -> Addr -> Addr -> [Addr] -> CombinedCtx -> FixAAMR r s e FixChange
doUnwind name n kaddr mkaddr addrs ctx = doBottom