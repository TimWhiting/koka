{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.AAC where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Full.AbstractValue
import Core.FlowAnalysis.Full.Monad
import Core.FlowAnalysis.Full.Primitives
import Core.Core
import Data.Int (Int)
import Common.Name
import Debug.Trace (trace)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Data.Maybe (fromJust)
import Compile.Module (Module(..))
import Common.Failure (HasCallStack)
import Type.Type (splitFunType, typeAny)
import Control.Monad (foldM)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)

-- 0CFA Allocation
alloc :: HasCallStack => FixInput -> LocalKont -> FixAACR r s e [Addr]
alloc (Cont _ _ _ (AChangeClos lam env) store xclos) (AppL nargs e env':ls) = do
  let names = lamArgNames lam
  if length names /= nargs then doBottom -- error ("alloc: " ++ show names ++ " " ++ show nargs)
  else do
    let addrs = repeat (contextId lam)
    return $ zip names addrs
alloc (Cont _ _ _ (AChangePrim n expr _) store xclos) (AppL nargs e0 env':ls) = do
  let addrs = repeat $ contextId e0
  let names =  map (\x -> TName (newHiddenName $ nameStem n ++ show x) typeAny Nothing) (take nargs [0..])
  return $ zip names addrs
alloc (Cont _ _ _ (AChangeConstr con env) store xclos) (AppL nargs e env':ls) = do
  case exprOfCtx con of
    Con tn _ -> do
      let addrs = repeat $ contextId e
          tp = typeOf tn
      case splitFunType tp of
        Just (args, _, _) -> return $ zip (map (\(n,t) -> TName n t Nothing) args) addrs
        Nothing -> return [(tn, contextId e)]

allocBindAddrs :: HasCallStack => DefGroup -> ExprContext -> FixAACR r s e [Addr]
allocBindAddrs (DefRec defs) expr = do
  let names = dfsTNames defs
  return $ zip names (repeat $ contextId expr)
allocBindAddrs (DefNonRec df) expr = return [(TName (defName df) (defType df) Nothing, contextId expr)]

doStep :: FixInput -> FixAACR r s e FixChange
doStep i = do
  memo i $ do
    -- trace ("Step: " ++ show i) $ return ()
    case i of
      Eval expr env store xclos local kont meta ->
        -- trace ("Eval: " ++ showSimpleContext expr) $ do
        case exprOfCtx expr of
          Lit l -> doStep $ Cont local kont meta (injLit l env) store xclos
          Var x _ -> do
            if isPrimitive x then
              let n = getName x in
              doStep $ Cont local kont meta (AChangePrim n expr env) store xclos
            else do
              -- trace ("Var: " ++ show x ++ " " ++ show env) $ return ()
              v <- storeLookup x env store
              doGC $ Cont local kont meta v store xclos
          Con _ _ -> do
            doStep $ Cont local kont meta (AChangeConstr expr env) store xclos
          App (TypeApp (Var name _) _) args _ | nameEffectOpen == getName name -> do
            f <- focusChild 1 expr
            doStep $ Eval f env store xclos local kont meta
          App f args _ -> do
            f <- focusChild 0 expr
            doStep $ Eval f env store xclos (AppL (length args) expr env : local) kont meta
          Lam args eff body -> do
            doStep $ Cont local kont meta (AChangeClos expr (limitEnv env (fvs expr))) store xclos
          TypeLam args body -> do
            doStep $ Cont local kont meta (AChangeClos expr (limitEnv env (fvs expr))) store xclos
          TypeApp e _ -> do
            e <- focusChild 0 expr
            doStep $ Eval e env store xclos local kont meta
          Case [e] bs -> do
            ex <- focusChild 0 expr
            doStep $ Eval ex env store xclos (CaseR expr env : local) kont meta
          Let binds body -> do
            ex <- focusChild 1 expr
            let bg = head binds
            addrs <- allocBindAddrs bg expr
            doStep $ Eval ex (extendEnv env (dgTNames bg) addrs) store xclos (LetL 0 (length binds) 0 (length $ defsOf bg) addrs expr env : local) kont meta
          _ -> error $ "doStep: " ++ show expr ++ " not handled"
      Cont [EndProgram] KEnd MEnd achange store xclos -> return $ AC achange
      Cont [EndProgram] KEnd meta achange store xclos -> error "Not handled yet" -- TODO: Handle the no-top condition
      Cont lc kont meta achange store xclos -> do
        KC l k <- doStep (Pop lc kont)
        case l of
          AppL n e p:ls -> do
            if n == 0 then do
              let AChangeClos lam env = achange
              body <- focusBody lam
              doGC $ Eval body env store xclos ls k meta
            else if n == 1 then do
              arge <- focusChild 1 e
              addrs <- alloc i l
              doGC $ Eval arge p store xclos (AppR achange addrs:ls) k meta
            else do
              arge <- focusChild 1 e
              -- trace ("AppL: " ++ show n ++ " " ++ show arge ++ " " ++ show p) $ return ()
              addrs <- alloc i l
              doGC $ Eval arge p store xclos (AppM achange addrs e 1 n p:ls) k meta
          AppM clos addrs e n t p:ls -> do
            arge <- focusChild (n + 1) e
            -- trace ("AppM: " ++ show n ++ " " ++ show arge ++ " " ++ show p) $ return ()
            let store' = extendStore store (addrs !! (n - 1)) achange
            if n + 1 == t then doGC $ Eval arge p store' xclos (AppR clos addrs:ls) k meta
            else doGC $ Eval arge p store' xclos (AppM clos addrs e (n + 1) t p:ls) k meta
          (AppR c@(AChangeClos clos env) addrs):ls -> do
            body <- focusBody clos
            let args = lamArgNames clos
            let store' = extendStore store (last addrs) achange
            -- (ExprContext, VEnv, VStore, KClos)
            let tau = (clos, env, store, xclos)
            addKont tau ls k
            -- trace ("AppR: " ++ show clos ++ " " ++ show (extendEnv env args addrs) ++ " " ++ show addrs) $ return ()
            doGC $ Eval body (extendEnv env args addrs) store' xclos [EndCall] (KPrecise tau) meta
          (AppR ccon@(AChangeConstr con env) addrs):ls -> do
            case exprOfCtx con of
              Con _ _ -> do
                let store' = extendStore store (last addrs) achange
                -- trace ("AppR: " ++ show con ++ " " ++ show addrs) $ return ()
                doGC $ Cont l k meta (AChangeConstr con (M.fromList (zip (tnamesCons (length addrs)) addrs))) store' xclos
          (AppR cprim@(AChangePrim p ctx env) addrs):ls -> do
            let store' = extendStore store (last addrs) achange
            res <- doPrimitive p addrs env store'
            doGC $ Cont ls k meta res store xclos
          LetL bgi bgn bi bn addrs e p:ls -> do 
            let dgs = letDefsOf e
            -- trace ("LetL: " ++ show bgi ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ show addrs) $ return ()
            let store' = extendStore store (addrs !! bi) achange
            if bgi + 1 == bgn && bi + 1 == bn then do
              -- trace ("LetL End") $ return ()
              body <- focusChild 0 e
              doGC $ Eval body (extendEnv p (dgsTNames dgs) addrs) store' xclos ls k meta
            else if bi + 1 /= bn then do
              -- trace ("LetL In Group") $ return ()
              bind <- focusLetDefBinding bgi bi e
              doGC $ Eval bind p store' xclos (LetL bgi bgn (bi + 1) bn addrs e p:ls) k meta
            else if bi + 1 == bn then do
              -- trace ("LetL End Group") $ return ()
              let bgi' = bgi + 1
              let bg = dgs !! bgi'
              bind <- focusLetDefBinding bgi' bi e
              addrs <- allocBindAddrs bg e
              doGC $ Eval bind (extendEnv p (dgTNames bg) addrs) store' xclos (LetL bgi' bgn 0 (length $ defsOf bg) addrs e p:ls) k meta
            else
              error "Cont LetL"
          (CaseR expr env): ls -> do
            case exprOfCtx expr of
              Case [e] bs -> do
                matchBranches achange (zip bs [1..])
                where
                  matchBranches :: HasCallStack => AChange -> [(Branch, Int)] -> FixAACR r s e FixChange
                  matchBranches achange [] = doBottom
                  matchBranches achange ((Branch [pat] body, n):bs) = do
                    matches <- matchBindPattern achange pat env store
                    -- trace ("MatchChange: " ++ show achange) $ return ()
                    case matches of
                      Just (venv, vstore) -> do
                        body <- focusChild n expr
                        let free = fvs body `S.difference` bv pat
                        doGC $ Eval body (limitEnv venv free) vstore xclos ls k meta
                      Nothing -> matchBranches achange bs
                  matchBindPattern :: HasCallStack => AChange -> Pattern -> VEnv -> VStore -> FixAACR r s e (Maybe (VEnv, VStore))
                  matchBindPattern achange pat venv vstore = do
                    case pat of
                      PatWild -> return $ Just (venv, vstore)
                      PatVar x pat' ->
                        let addr = (x, contextId expr)
                            env' = M.insert x addr env
                        in matchBindPattern achange pat' env' (extendStore vstore addr achange)
                      PatCon con pats _ _ _ _ _ _ -> do
                        case achange of 
                          AChangeConstr acon aenv -> do
                            case exprOfCtx acon of
                              Con c _ | c == con -> do
                                -- trace ("Match: " ++ show c ++ " " ++ show con) $ return ()
                                foldM (\isMatch (pat, i) -> do
                                  case isMatch of
                                    Just (venv, vstore) -> do
                                      -- trace ("Match: " ++ show acon ++ "--" ++ show con) $ return ()
                                      v <- storeLookup (TName (newName $ "con" ++ show i) typeAny Nothing) aenv vstore
                                      matchBindPattern v pat venv vstore
                                    _ -> return Nothing
                                  ) (Just (venv, vstore)) (zip pats [0..])
                              _ -> return Nothing
                          _ -> return Nothing
                      PatLit x ->
                        case (x, achange) of
                          (LitInt i, AChangeLit (LiteralChangeInt (LChangeSingle i2)) _) -> if i == i2 then return (Just (venv, vstore)) else doBottom
                          (LitFloat f, AChangeLit (LiteralChangeFloat (LChangeSingle f2)) _) -> if f == f2 then return (Just (venv, vstore)) else doBottom
                          (LitChar c, AChangeLit (LiteralChangeChar (LChangeSingle c2)) _) -> if c == c2 then return (Just (venv, vstore)) else doBottom
                          (LitString s, AChangeLit (LiteralChangeString (LChangeSingle s2)) _) -> if s == s2 then return (Just (venv, vstore)) else doBottom
                          (LitInt i, AChangeLit (LiteralChangeInt LChangeTop) _) -> each [return (Just (venv, vstore)), return Nothing] -- TODO: Also evaluate other branches
                          (LitFloat f, AChangeLit (LiteralChangeFloat LChangeTop) _) -> each [return (Just (venv, vstore)), return Nothing]
                          (LitChar c, AChangeLit (LiteralChangeChar LChangeTop) _) -> each [return (Just (venv, vstore)), return Nothing]
                          (LitString s, AChangeLit (LiteralChangeString LChangeTop) _) -> each [return (Just (venv, vstore)), return Nothing]
                          _ -> doBottom
              _ -> error "Cont CaseR"
          [EndCall] -> return $ AC achange -- TODO: Pop meta continuation
          [EndProgram] -> return $ AC achange
          _ -> error $ "Cont: " ++ show l
      KStoreGet ctx -> doBottom
      CStoreGet meta -> doBottom
      Pop [EndCall] (KPrecise ctx) -> do
        KC l k <- doStep $ KStoreGet ctx
        doStep $ Pop l k
      Pop (l:ls) kont -> return $ KC (l:ls) kont
      -- Pop [] (Just approx@KApprox ctx) = do
      --   precise <- forT ctx
      --   doStep (Pop l k)
      NoTop [EndCall] KEnd -> return $ BC True
      NoTop [EndCall] k -> do
        KC l k <- doStep $ Pop [EndCall] k
        doStep $ NoTop l k -- TODO: can we assume no new values get added & get a set and use (or)
      NoTop (l:ls) k -> return $ BC False
      


-- TODO: Garbage collection
-- TODO: Delimited Control

llKont :: Kont -> S.Set Kont -> FixAACR r s e (S.Set Addr)
llKont kont seen =
  if kont `S.member` seen then return S.empty
  else do 
    case kont of
      KEnd -> return S.empty
      KPrecise ctx@(_, env, store, xclos) -> do
        let envAddrs = llEnv env
        KC l k <- doStep $ KStoreGet ctx
        reckaddrs <- llKont k (S.insert kont seen)
        return $ S.unions [envAddrs, reckaddrs, llLKont l]

llMeta :: MetaKont -> FixAACR r s e (S.Set Addr)
llMeta kont = return $ S.empty

doGC :: FixInput -> FixAACR r s e FixChange
doGC i = do
  i' <- gc i
  doStep i'

gc :: FixInput ->  FixAACR r s e FixInput
gc (Eval e env store kclos klocal kont meta) = do
  let env' = limitEnv env (fv (exprOfCtx e)) 
  let laddrs = llLKont klocal
  kaddrs <- llKont kont S.empty
  maddrs <- llMeta meta
  let live = liveAddrs store (S.unions [llEnv env', laddrs, kaddrs, maddrs])
  let store' = limitStore store live
  return $ Eval e env' store' kclos klocal kont meta
gc (Cont l k meta achange store xclos) = do
  let laddrs = llLKont l
  let vaddrs = llV achange
  kaddrs <- llKont k S.empty
  maddrs <- llMeta meta
  let live = liveAddrs store (S.unions [vaddrs, laddrs, kaddrs, maddrs])
  let store' = limitStore store live
  return $ Cont l k meta achange store' xclos