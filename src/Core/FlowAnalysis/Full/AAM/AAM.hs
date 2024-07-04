{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.AAM.AAM where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Full.AbstractValue
import Core.FlowAnalysis.Full.AAM.Monad
import Core.FlowAnalysis.Full.Primitives
import Core.Core
import Data.Int (Int)
import Common.Name
import Debug.Trace (trace)
import Common.NamePrim (nameOpen, nameEffectOpen, nameHandle, namePerform, nameClause)
import Data.Maybe (fromJust)
import Compile.Module (Module(..))
import Common.Failure (HasCallStack)
import Type.Type (splitFunType, typeAny, splitFunScheme, Effect, typeTotal, effectExtend, extractEffectExtend)
import Control.Monad (foldM)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)
import Type.Pretty (defaultEnv, ppType)
import Lib.PPrint (hcat, tupled, vcat, text)

-- 0CFA Allocation
alloc :: HasCallStack => FixInput -> Frame -> FixAAMR r s e [Addr]
alloc (Cont (AChangeClos lam env) env2 store kstore kont) (AppL nargs e env') = do
  let names = lamArgNames lam
  if length names /= nargs then doBottom -- error ("alloc: " ++ show names ++ " " ++ show nargs)
  else do
    let addrs = repeat (contextId lam)
    return $ zip names addrs
alloc (Cont (AChangePrim n expr _) env2 store kstore kont) (AppL nargs e0 env') = do
  let addrs = repeat $ contextId e0
  let names =  map (\x -> TName (newHiddenName $ nameStem (getName n) ++ show x) typeAny Nothing) (take nargs [0..])
  return $ zip names addrs
alloc (Cont (AChangeConstr con env) env2 store kstore kont) (AppL nargs e env') = do
  case exprOfCtx con of
    Con tn _ -> do
      let addrs = repeat $ contextId e
          tp = typeOf tn
      case splitFunScheme tp of
        Just (_, _, args, _, _) ->
          if nargs /= length args then error "Wrong number of arguments "
          else return $ zip (map (\(n,t) -> TName n t Nothing) args) addrs
        Nothing -> return [(tn, contextId e)]

allocBindAddrs :: HasCallStack => DefGroup -> ExprContext -> FixAAMR r s e [Addr]
allocBindAddrs (DefRec defs) expr = do
  let names = dfsTNames defs
  return $ zip names (repeat $ contextId expr)
allocBindAddrs (DefNonRec df) expr = return [(TName (defName df) (defType df) Nothing, contextId expr)]

doStep :: HasCallStack => FixInput -> FixAAMR r s e FixChange
doStep i =
  memo i $ do
    trace ("Step: " ++ show i) $ return ()
    case i of
      Eval expr env store kstore kont ->
        -- trace ("Eval: " ++ showSimpleContext expr) $ do
        case exprOfCtx expr of
          Lit l -> doGC $ Cont (injLit l env) M.empty store kstore kont
          Var x _ -> do
            if isPrimitive x then do
              doGC $ Cont (AChangePrim x expr env) M.empty store kstore kont
            else do
              -- trace ("Var: " ++ show x ++ " " ++ show env) $ return ()
              -- trace ("Var: " ++ show (contextOf expr)) $ return ()
              v <- storeLookup x env store
              doGC $ Cont v M.empty store kstore kont
          Con _ _ -> do
            doGC $ Cont (AChangeConstr expr env) M.empty store kstore kont
          App (TypeApp (Var name _) tps@[_, _, tp, _, _]) args _ | nameHandle == getName name -> do
            c <- focusChild 1 expr
            -- trace ("Handle: " ++ show (vcat $ map (text . show) tps)) $ return ()
            doGC $ Eval c env store kstore (HandleL [] tp expr env:kont)
          App (TypeApp (Var name _) _) args _ | nameEffectOpen == getName name -> do
            f <- focusChild 1 expr
            doGC $ Eval f env store kstore kont
          App (TypeApp (Var name _) _) args _ | namePerform 0 == getName name -> do
            trace ("Perform0: " ++ show expr) $ return ()
            select <- focusChild 2 expr
            let kaddr = Kont (expr, env)
            let eff =
                  case contextOf <$> enclosingLambda expr of
                    Just (Just lam) -> case exprOfCtx lam of
                      Lam args eff body -> eff
                      _ -> error "doStep: Perform"
            doGC $ Eval select env store (kstoreExtend kaddr kont kstore) [OpL eff kaddr]
          App f args _ -> do
            f <- focusChild 0 expr
            doGC $ Eval f env store kstore (AppL (length args) expr env:kont)
          Lam args eff body -> do
            doGC $ Cont (AChangeClos expr (limitEnv env (fvs expr))) M.empty store kstore kont
          TypeLam args body -> do
            doGC $ Cont (AChangeClos expr (limitEnv env (fvs expr))) M.empty store kstore kont
          TypeApp (TypeLam _ _) _ -> do
            -- trace ("TypeApp: " ++ showSimpleContext e) $ return ()
            doGC $ Cont (AChangeClos expr (limitEnv env (fvs expr))) M.empty store kstore kont
          TypeApp (Var _ _) _ -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store kstore kont
          TypeApp (Con _ _) _ -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store kstore kont
          Case [e] bs -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store kstore (CaseR expr env:kont)
          Let binds body -> do
            ex <- focusChild 1 expr
            -- trace ("Let: " ++ show binds ++ showSimpleContext ex) $ return ()
            let bg = head binds
            addrs <- allocBindAddrs bg expr
            let env' = extendEnv env (dgTNames bg) addrs
            doGC $ Eval ex env' store kstore (LetL 0 (length binds) 0 (length $ defsOf bg) addrs expr env':kont)
          _ -> error $ "doStep: " ++ show expr ++ " not handled"
      Cont achange env store kstore kont -> do
        -- trace ("Cont: " ++ show l ++ " " ++ show k) $ return ()
        case kont of
          [OpL eff kaddr] -> do
            let AChangeClos select senv = achange
            child <- focusChild 0 select
            doGC $ Eval child senv store kstore [OpL2 eff kaddr]
          [OpL2 eff kaddr] -> do
            handframes <- getHandler eff kaddr kstore
            let HandleR [tag, hnd, ret, act] ef e p:ls = handframes
            -- Need to allocate
            let AChangeClos select senv = achange
            body <- focusBody select -- Body of the select 
            let names = lamArgNames select
            let addrs = zip names (repeat (contextId select))
            doGC $ Eval body (extendEnv senv names addrs) (extendStore store (head addrs) hnd) kstore (OpR [] kaddr:handframes)
          OpR changes kaddr:hndframes -> do -- This is realy OpRTail, we should add a 
            let AChangeClos op openv = achange
            case M.lookup kaddr kstore of 
              Nothing -> doBottom
              Just konts -> do
                callopframes <- each (map return (S.toList konts))
                opbod <- focusBody op
                 -- Using these frames here only works for tail call no ops, but resume is not bound even for tail call
                doGC $ Eval opbod openv store kstore callopframes
          HandleR [tag, hnd, retClos, act] ef e p:ls -> do
            trace ("HandleR: " ++ show (length [tag, hnd, retClos, act])) $ return ()
            let AChangeClos ret env = retClos
            let names = lamArgNames ret
            let addrs = zip names (repeat (contextId ret))
            body <- focusBody ret
            doGC $ Eval body (extendEnv env names addrs) (extendStore store (head addrs) achange) kstore ls
          HandleL changes ef e p:ls -> do
            trace ("HandleL: " ++ show (length changes)) $ return ()
            if length changes == 3 then do
              let AChangeClos lam env = achange
              body <- focusBody lam
              let kaddr = Kont (lam, env)
              doGC $ Eval body env store (kstoreExtend kaddr (HandleR (changes ++ [achange]) ef e p:ls) kstore) [EndCall kaddr]
            else do
              nextparam <- focusChild (length changes + 2) e
              doGC $ Eval nextparam p store kstore (HandleL (changes ++ [achange]) ef e p:ls)
          l@(AppL n e p):ls -> do
            if n == 0 then do
              let AChangeClos lam env = achange
              body <- focusBody lam
              let kaddr = Kont (lam, env)
              doGC $ Eval body env store (kstoreExtend kaddr ls kstore) [EndCall kaddr]
            else if n == 1 then do
              arge <- focusChild 1 e
              addrs <- alloc i l
              -- trace ("AppL: " ++ show n ++ " " ++ show arge ++ " " ++ show p) $ return ()
              -- k' <- 
              doGC $ Eval arge p store kstore (AppR achange addrs:ls)
            else do
              arge <- focusChild 1 e
              -- trace ("AppL: " ++ show n ++ " " ++ show arge ++ " " ++ show p) $ return ()
              addrs <- alloc i l
              doGC $ Eval arge p store kstore (AppM achange addrs e 1 n p:ls)
          AppM clos addrs e n t p:ls -> do
            arge <- focusChild (n + 1) e
            -- trace ("AppM: " ++ show n ++ " " ++ show arge ++ " " ++ show clos) $ return ()
            let store' = extendStore store (addrs !! (n - 1)) achange
            if n + 1 == t then do
              -- trace ("AppRM: " ++ show clos) $ return ()
              doGC $ Eval arge p store' kstore (AppR clos addrs:ls)
            else do
              doGC $ Eval arge p store' kstore (AppM clos addrs e (n + 1) t p:ls)
          (AppR c@(AChangePrim p clos env) addrs):ls | getName p == nameClause "tail" 0 -> do
            trace "ClauseTail0" $ return ()
            doGC $ Cont achange M.empty store kstore ls
          (AppR c@(AChangeClos clos env) addrs):ls -> do
            -- trace ("AppR: " ++ show c ++ " " ++ show ls) $ return ()
            body <- focusBody clos
            let args = lamArgNames clos
            let store' = extendStore store (last addrs) achange
            let kaddr = Kont (clos, env)
            -- (ExprContext, VEnv, VStore, KClos)
            -- trace ("AppR: " ++ show c ++ " " ++ show ls) $ return ()
            doGC $ Eval body (extendEnv env args addrs) store' (kstoreExtend kaddr ls kstore) [EndCall kaddr]
          (AppR ccon@(AChangeConstr con env) addrs):ls -> do
            case exprOfCtx con of
              Con _ _ -> do
                let store' = extendStore store (last addrs) achange
                let env' = M.fromList (zip (tnamesCons (length addrs)) addrs)
                -- trace ("AppRCon: " ++ show con ++ " " ++ show env' ++ " " ++ show addrs) $ return ()
                -- trace ("AppRCon:\n" ++ showStore store) $ return ()
                doGC $ Cont (AChangeConstr con env') M.empty store' kstore ls
          (AppR cprim@(AChangePrim p ctx env) addrs):ls -> do
            -- trace ("Prim store " ++ showStore store) $ return ()
            let store' = extendStore store (last addrs) achange
            res <- doPrimitive (getName p) addrs env store'
            -- trace ("Primitive Result " ++ show cprim ++ " " ++ show res ++ " " ++ show ls) $ return ()
            doGC $ Cont res M.empty store' kstore ls
          LetL bgi bgn bi bn addrs e p:ls -> do
            let dgs = letDefsOf e
            -- trace ("LetL: " ++ show bgi ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ show addrs) $ return ()
            let store' = extendStore store (addrs !! bi) achange
            if bgi + 1 == bgn && bi + 1 == bn then do
              -- trace ("LetL End") $ return ()
              body <- focusChild 0 e
              doGC $ Eval body (extendEnv p (dgsTNames dgs) addrs) store' kstore ls
            else if bi + 1 /= bn then do
              -- trace ("LetL In Group") $ return ()
              bind <- focusLetDefBinding bgi bi e
              doGC $ Eval bind p store' kstore (LetL bgi bgn (bi + 1) bn addrs e p:ls)
            else if bi + 1 == bn then do
              -- trace ("LetL End Group") $ return ()
              let bgi' = bgi + 1
              let bg = dgs !! bgi'
              bind <- focusLetDefBinding bgi' bi e
              addrs' <- allocBindAddrs bg e
              let env' = extendEnv p (dgTNames bg) addrs'
              doGC $ Eval bind env' store' kstore (LetL bgi' bgn 0 (length $ defsOf bg) addrs' e p:ls)
            else
              error "Cont LetL"
          (CaseR expr env):ls -> do
            case exprOfCtx expr of
              Case [e] bs -> do
                matchBranches achange (zip bs [1..])
                where
                  matchBranches :: HasCallStack => AChange -> [(Branch, Int)] -> FixAAMR r s e FixChange
                  matchBranches achange [] = doBottom
                  matchBranches achange ((Branch [pat] body, n):bs) = do
                    matches <- matchBindPattern achange pat env store
                    -- trace ("MatchChange: " ++ show achange) $ return ()
                    case matches of
                      Just (venv, vstore) -> do
                        body <- focusChild n expr
                        let free = fvs body
                        -- trace ("Match: " ++ show pat ++ " " ++ show venv ++ "\n") $ return ()
                        doGC $ Eval body venv vstore kstore ls
                      Nothing -> matchBranches achange bs
                  matchBindPattern :: HasCallStack => AChange -> Pattern -> VEnv -> VStore -> FixAAMR r s e (Maybe (VEnv, VStore))
                  matchBindPattern achange pat venv vstore = do
                    case pat of
                      PatWild -> return $ Just (venv, vstore)
                      PatVar x pat' -> do
                        let addr = (x, contextId expr)
                            env' = M.insert x addr venv
                        -- trace ("Match: " ++ show x ++ " " ++ show addr ++ " " ++ show env') $ return ()
                        matchBindPattern achange pat' env' (extendStore vstore addr achange)
                      PatCon con pats _ _ _ _ _ _ -> do
                        case achange of
                          AChangeConstr acon aenv -> do
                            case exprOfCtx acon of
                              Con c _ | c == con -> do
                                -- trace ("Match: " ++ show c ++ " " ++ show con) $ return ()
                                foldM (\isMatch (pat, i) -> do
                                  case isMatch of
                                    Just (venv, vstore) -> do
                                      -- trace ("Match: " ++ show acon ++ "--" ++ show aenv ++ " " ++ show i) $ return ()
                                      -- trace ("Match: \n" ++ showStore vstore) $ return ()
                                      v <- storeLookup (TName (newName $ "con" ++ show i) typeAny Nothing) aenv vstore
                                      matchBindPattern v pat venv vstore
                                    _ -> return Nothing
                                  ) (Just (venv, vstore)) (zip pats [0..])
                              _ -> return Nothing
                          _ -> return Nothing
                      PatLit x ->
                        case (x, achange) of
                          (LitInt i, AChangeLit (LiteralChangeInt (LChangeSingle i2))) -> if i == i2 then return (Just (venv, vstore)) else doBottom
                          (LitFloat f, AChangeLit (LiteralChangeFloat (LChangeSingle f2))) -> if f == f2 then return (Just (venv, vstore)) else doBottom
                          (LitChar c, AChangeLit (LiteralChangeChar (LChangeSingle c2))) -> if c == c2 then return (Just (venv, vstore)) else doBottom
                          (LitString s, AChangeLit (LiteralChangeString (LChangeSingle s2))) -> if s == s2 then return (Just (venv, vstore)) else doBottom
                          (LitInt i, AChangeLit (LiteralChangeInt LChangeTop)) -> each [return (Just (venv, vstore)), return Nothing] -- TODO: Also evaluate other branches
                          (LitFloat f, AChangeLit (LiteralChangeFloat LChangeTop)) -> each [return (Just (venv, vstore)), return Nothing]
                          (LitChar c, AChangeLit (LiteralChangeChar LChangeTop)) -> each [return (Just (venv, vstore)), return Nothing]
                          (LitString s, AChangeLit (LiteralChangeString LChangeTop)) -> each [return (Just (venv, vstore)), return Nothing]
                          _ -> doBottom
              _ -> error "Cont CaseR"
          [EndCall k] -> do
            let res = M.lookup k kstore
            l <- each $ map return (maybe [] S.toList res)
            doGC $ Cont achange M.empty store kstore l
          [EndProgram] ->
            return $ AC achange

getHandler :: HasCallStack => Effect -> Kont -> KStore -> FixAAMR r s e [Frame]
getHandler eff kont kstore = do
  -- trace ("getHandler: " ++ show kont) $ return []
  case M.lookup kont kstore of
    Just frames -> each (map (\frames -> getHandlerF eff frames kstore) (S.toList frames))
    Nothing -> error "getHandler: Not found"

getHandlerF :: HasCallStack => Effect -> [Frame] -> KStore -> FixAAMR r s e [Frame]
getHandlerF eff frames kstore = do
  -- trace ("getHandlerF: " ++ show frames) $ return []
  case frames of
    (HandleR changes ef e p):ls | fst (extractEffectExtend ef) == fst (extractEffectExtend eff) -> return frames
    -- (HandleL changes ef e p):ls | ef /= eff -> trace ("getHandlerX:\n" ++ show ef ++ "\n" ++ show eff) $ return []
    [EndCall k] -> getHandler eff k kstore
    f:ls -> getHandlerF eff ls kstore
    [] -> error "getHandlerF: Not found"

doGC :: FixInput -> FixAAMR r s e FixChange
doGC i = do
  i' <- gc i
  doStep i'

-- TODO: Delimited Control