{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.AAC.AAC where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Full.AbstractValue
import Core.FlowAnalysis.Full.AAC.Monad
import Core.FlowAnalysis.Full.Primitives
import Core.Core
import Data.Int (Int)
import Common.Name
import Debug.Trace (trace)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Data.Maybe (fromJust)
import Compile.Module (Module(..))
import Common.Failure (HasCallStack)
import Type.Type (splitFunType, typeAny, splitFunScheme)
import Control.Monad (foldM)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)

-- 0CFA Allocation
alloc :: HasCallStack => FixInput -> LocalKont -> FixAACR r s e [Addr]
alloc (Cont _ _ _ (AChangeClos lam env) store xclos (KTime l time)) (AppL nargs e env':ls) = do
  let names = lamArgNames lam
  if length names /= nargs then doBottom -- error ("alloc: " ++ show names ++ " " ++ show nargs)
  else do
    let addrs = repeat (contextId lam)
    return $ zip3 names addrs (repeat time)
alloc (Cont _ _ _ (AChangePrim n expr _) store xclos (KTime l time)) (AppL nargs e0 env':ls) = do
  let addrs = repeat $ contextId e0
  let names =  map (\x -> TName (newHiddenName $ nameStem (getName n) ++ show x) typeAny Nothing) (take nargs [0..])
  return $ zip3 names addrs (repeat time)
alloc (Cont _ _ _ (AChangeConstr con env) store xclos (KTime l time)) (AppL nargs e env':ls) = do
  case exprOfCtx con of
    Con tn _ -> do
      let addrs = repeat $ contextId e
          tp = typeOf tn
      case splitFunScheme tp of
        Just (_, _, args, _, _) ->
          if nargs /= length args then error "Wrong number of arguments "
          else return $ zip3 (map (\(n,t) -> TName n t Nothing) args) addrs (repeat time)
        Nothing -> return [(tn, contextId e, time)]

allocBindAddrs :: HasCallStack => DefGroup -> ExprContext -> Time -> FixAACR r s e [Addr]
allocBindAddrs (DefRec defs) expr (KTime l time) = do
  let names = dfsTNames defs
  return $ zip3 names (repeat $ contextId expr) (repeat time)
allocBindAddrs (DefNonRec df) expr (KTime l time) = return [(TName (defName df) (defType df) Nothing, contextId expr, time)]

doStep :: HasCallStack => FixInput -> FixAACR r s e FixChange
doStep i =
  memo i $ do
    -- trace ("Step: " ++ show i) $ return ()
    case i of
      Eval expr env store xclos local kont meta time ->
        -- trace ("Eval: " ++ showSimpleContext expr) $ do
        case exprOfCtx expr of
          Lit l -> doGC $ Cont local kont meta (injLit l env) store xclos time
          Var x _ -> do
            if isPrimitive x then
              doGC $ Cont local kont meta (AChangePrim x expr env) store xclos time
            else do
              -- trace ("Var: " ++ show x ++ " " ++ show env) $ return ()
              v <- storeLookup x env store
              doGC $ Cont local kont meta v store xclos time
          Con _ _ -> do
            doGC $ Cont local kont meta (AChangeConstr expr env) store xclos time
          App (TypeApp (Var name _) _) args _ | nameEffectOpen == getName name -> do
            f <- focusChild 1 expr
            doGC $ Eval f env store xclos local kont meta time
          App f args _ -> do
            f <- focusChild 0 expr
            doGC $ Eval f env store xclos (AppL (length args) expr env : local) kont meta time
          Lam args eff body -> do
            doGC $ Cont local kont meta (AChangeClos expr (limitEnv env (fvs expr))) store xclos time
          TypeLam args body -> do
            doGC $ Cont local kont meta (AChangeClos expr (limitEnv env (fvs expr))) store xclos time
          TypeApp (TypeLam _ _) _ -> do
            -- trace ("TypeApp: " ++ showSimpleContext e) $ return ()
            doGC $ Cont local kont meta (AChangeClos expr (limitEnv env (fvs expr))) store xclos time
          TypeApp (Var _ _) _ -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store xclos local kont meta time
          TypeApp (Con _ _) _ -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store xclos local kont meta time
          Case [e] bs -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store xclos (CaseR expr env : local) kont meta time
          Let binds body -> do
            ex <- focusChild 1 expr
            -- trace ("Let: " ++ show binds ++ showSimpleContext ex) $ return ()
            let bg = head binds
            addrs <- allocBindAddrs bg expr time
            let env' = extendEnv env (dgTNames bg) addrs
            doGC $ Eval ex env' store xclos (LetL 0 (length binds) 0 (length $ defsOf bg) addrs expr env': local) kont meta time
          _ -> error $ "doStep: " ++ show expr ++ " not handled"
      Cont [EndProgram] KEnd2 MEnd achange store xclos time -> return $ AC achange
      Cont [EndProgram] KEnd2 meta achange store xclos time -> error "Not handled yet" -- TODO: Handle the no-top condition
      Cont lc kont meta achange store xclos time@(KTime tlabel contour) -> do
        KC l k <- pop lc kont
        -- trace ("Cont: " ++ show l ++ " " ++ show k) $ return ()
        case l of
          AppL n e p:ls -> do
            if n == 0 then do
              let AChangeClos lam env = achange
              let tau = (achange, achange, store, xclos)
              addKont tau ls k
              body <- focusBody lam
              doGC $ Eval body env store xclos [EndCall] (KPrecise tau) meta time
            else if n == 1 then do
              arge <- focusChild 1 e
              addrs <- alloc i l
              -- trace ("AppL: " ++ show n ++ " " ++ show arge ++ " " ++ show p) $ return ()
              doGC $ Eval arge p store xclos (AppR achange addrs:ls) k meta time
            else do
              arge <- focusChild 1 e
              -- trace ("AppL: " ++ show n ++ " " ++ show arge ++ " " ++ show p) $ return ()
              addrs <- alloc i l
              doGC $ Eval arge p store xclos (AppM achange addrs e 1 n p:ls) k meta time
          AppM clos addrs e n t p:ls -> do
            arge <- focusChild (n + 1) e
            -- trace ("AppM: " ++ show n ++ " " ++ show arge ++ " " ++ show clos) $ return ()
            let store' = extendStore store (addrs !! (n - 1)) achange
            if n + 1 == t then do
              -- trace ("AppRM: " ++ show clos) $ return ()
              doGC $ Eval arge p store' xclos (AppR clos addrs:ls) k meta time
            else doGC $ Eval arge p store' xclos (AppM clos addrs e (n + 1) t p:ls) k meta time
          (AppR c@(AChangeClos clos env) addrs):ls -> do
            -- trace ("AppR: " ++ show c ++ " " ++ show ls) $ return ()
            body <- focusBody clos
            let args = lamArgNames clos
            let store' = extendStore store (last addrs) achange
            -- (ExprContext, VEnv, VStore, KClos)
            let tau = (c, achange, store, xclos)
            -- trace ("AddKont " ++ show tau) $ return ()
            addKont tau ls k
            -- trace ("AppR: " ++ show c ++ " " ++ show ls) $ return ()
            doGC $ Eval body (extendEnv env args addrs) store' xclos [EndCall] (KPrecise tau) meta time
          (AppR ccon@(AChangeConstr con env) addrs):ls -> do
            case exprOfCtx con of
              Con _ _ -> do
                let store' = extendStore store (last addrs) achange
                let env' = M.fromList (zip (tnamesCons (length addrs)) addrs)
                -- trace ("AppRCon: " ++ show con ++ " " ++ show env' ++ " " ++ show addrs) $ return ()
                -- trace ("AppRCon:\n" ++ showStore store) $ return ()
                doGC $ Cont ls k meta (AChangeConstr con env') store' xclos time
          (AppR cprim@(AChangePrim p ctx env) addrs):ls -> do
            -- trace ("Prim store " ++ showStore store) $ return ()
            let store' = extendStore store (last addrs) achange
            res <- doPrimitive (getName p) addrs env store'
            -- trace ("Primitive Result " ++ show cprim ++ " " ++ show res ++ " " ++ show ls) $ return ()
            doGC $ Cont ls k meta res store' xclos time
          LetL bgi bgn bi bn addrs e p:ls -> do
            let dgs = letDefsOf e
            -- trace ("LetL: " ++ show bgi ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ show addrs) $ return ()
            let store' = extendStore store (addrs !! bi) achange
            if bgi + 1 == bgn && bi + 1 == bn then do
              -- trace ("LetL End") $ return ()
              body <- focusChild 0 e
              doGC $ Eval body (extendEnv p (dgsTNames dgs) addrs) store' xclos ls k meta time
            else if bi + 1 /= bn then do
              -- trace ("LetL In Group") $ return ()
              bind <- focusLetDefBinding bgi bi e
              doGC $ Eval bind p store' xclos (LetL bgi bgn (bi + 1) bn addrs e p:ls) k meta time
            else if bi + 1 == bn then do
              -- trace ("LetL End Group") $ return ()
              let bgi' = bgi + 1
              let bg = dgs !! bgi'
              bind <- focusLetDefBinding bgi' bi e
              addrs' <- allocBindAddrs bg e time
              let env' = extendEnv p (dgTNames bg) addrs'
              doGC $ Eval bind env' store' xclos (LetL bgi' bgn 0 (length $ defsOf bg) addrs' e env':ls) k meta time
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
                        let free = fvs body
                        -- trace ("Match: " ++ show pat ++ " " ++ show venv ++ "\n") $ return ()
                        doGC $ Eval body venv vstore xclos ls k meta time
                      Nothing -> matchBranches achange bs
                  matchBindPattern :: HasCallStack => AChange -> Pattern -> VEnv -> VStore -> FixAACR r s e (Maybe (VEnv, VStore))
                  matchBindPattern achange pat venv vstore = do
                    case pat of
                      PatWild -> return $ Just (venv, vstore)
                      PatVar x pat' -> do
                        let addr = (x, contextId expr, contour)
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
          [EndCall] ->
            doGC $ Cont [EndCall] k meta achange store xclos time
          [EndProgram] ->
            doGC $ Cont [EndProgram] k meta achange store xclos time
          _ -> error $ "Cont: " ++ show l
      KStoreGet ctx -> doBottom
      KApproxGet ctx -> doBottom
      CStoreGet meta -> doBottom


      -- NoTop [EndCall] KEnd -> return $ BC True
      -- NoTop [EndCall] k -> do
      --   KC l k <- doStep $ Pop [EndCall] k
      --   doStep $ NoTop l k -- TODO: can we assume no new values get added & get a set and use (or)
      -- NoTop (l:ls) k -> return $ BC False
pop :: LocalKont -> Kont -> FixAACR r s e FixChange
pop lk k = do
  res <- popS lk k S.empty
  each (map (\(l, k) -> return (KC l k)) (S.toList res))

popS :: LocalKont -> Kont -> S.Set Kont -> FixAACR r s e (S.Set (LocalKont, Kont))
popS [EndCall] k@(KPrecise ctx) seen = do
  if S.member k seen then return S.empty -- return $ KC (l:ls) kont
  else do
    KC l k <- doStep $ KStoreGet ctx
    -- trace ("Pop: " ++ show ctx ++ "\ngives:\n" ++ show l ++ " " ++ show k) $ return ()
    rest <- popS l k (S.insert k seen)
    return $ S.insert ([EndCall], k) rest
popS (l:ls) kont seen = return (S.singleton (l:ls, kont))
-- Pop [] (Just approx@KApprox ctx) = do
--   precise <- forT ctx
--   doStep (Pop l k)

doGC :: FixInput -> FixAACR r s e FixChange
doGC i = do
  i' <- gc i
  doStep i'

-- TODO: Delimited Control