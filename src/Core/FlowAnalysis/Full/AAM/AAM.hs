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
import Core.FlowAnalysis.Full.AAM.DelimitedTransform
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

kLimit :: Int
kLimit = 2

lamAddrs :: ExprContext -> Time -> ([TName], [Addr])
lamAddrs lam (KTime l time) =
  let names = lamArgNames lam
      addrs = zip3 names (repeat (contextId lam)) (repeat time)
  in (names, addrs)

allocBindAddrs :: HasCallStack => DefGroup -> ExprContext -> Time -> FixAAMR r s e [Addr]
allocBindAddrs (DefRec defs) expr (KTime l cont) = do
  let names = dfsTNames defs
  return $ zip3 names (repeat $ contextId expr) (repeat cont)
allocBindAddrs (DefNonRec df) expr (KTime l cont) =
  return [(TName (defName df) (defType df) Nothing, contextId expr, cont)]

extend :: VEnv -> VStore -> [TName] -> [Addr] -> [AChange] -> (VEnv, VStore)
extend env store names addrs changes =
  (extendEnv env names addrs, extendStoreAll store addrs changes)

integrate :: Maybe ExprContext -> Contour -> Contour
integrate (Just e) (KContour old) = KContour $ take kLimit (e:old)
integrate Nothing c = c


--TODO: select-op(h)(v) ==> \v,s -> Shift0 \k -> \h -> h(OpParams(s,v,fn(y) k(y,h)))
--TODO: Handle hnd e_body x.e_return ==>
--   let h_x = \o -> runop(o) -- runop is primitive
--        OpParams(s,v,k) -> s(hnd)(v,k)
--        OpParams(s,v,k) -> Shift0 \k' -> \h -> h(OpParams(s,v,fn(y) k'(k(y,h))))
--   <e_body|\(x,h) -> e_return>(h_x) -- <|> is primitive

-- 0CFA Allocation
alloc :: HasCallStack => FixInput -> Frame -> FixAAMR r s e [Addr]
alloc (Cont (AChangeKont k kr) store kstore lkont kont mkont (KTime l time)) (AppL nargs e0 env') = do
  let names = [TName (newHiddenName $ "k" ++ show x) typeAny Nothing | x <- [0..nargs - 1]]
  return $ zip3 names (repeat $ contextId e0) (repeat time)
alloc (Cont (AChangeClos lam env) store kstore lkont kont mkont (KTime l time)) (AppL nargs e env') = do
  let names = lamArgNames lam
  if length names /= nargs then doBottom -- error ("alloc: " ++ show names ++ " " ++ show nargs)
  else do
    let addrs = repeat (contextId lam)
    return $ zip3 names addrs (repeat time)
alloc (Cont (AChangePrim n expr _) store kstore lkont kont mkont (KTime l time)) (AppL nargs e0 env') = do
  let addrs = repeat $ contextId e0
      names =  map (\x -> TName (newHiddenName $ nameStem (getName n) ++ show x) typeAny Nothing) (take nargs [0..])
  return $ zip3 names addrs (repeat time)
alloc (Cont (AChangeConstr con env) store kstore lkont kont mkont (KTime l time)) (AppL nargs e env') = do
  case exprOfCtx con of
    Con tn _ -> do
      let addrs = repeat $ contextId e
          tp = typeOf tn
      case splitFunScheme tp of
        Just (_, _, args, _, _) ->
          if nargs /= length args then error "Wrong number of arguments "
          else return $ zip3 (map (\(n,t) -> TName n t Nothing) args) addrs (repeat time)
        Nothing -> return [(tn, contextId e, time)]

newTime :: Time -> FixInput -> Maybe Frame -> Time
newTime (KTime local old) (Cont (AChangeClos _ _) _ _ _ _ _ _) (Just (AppR{})) = KTime Nothing (integrate local old)
newTime (KTime local old) (Cont{}) (Just (OpR{})) = KTime Nothing (integrate local old)
newTime time (Cont{}) _ = time
newTime old@(KTime _ k) (Eval e1 _ _ _ _ _ _ _) Nothing = 
  case exprOfCtx e1 of
    App{} -> KTime (Just e1) k
    TypeApp{} -> KTime (Just e1) k
    _ -> old

isNamePerform :: Name -> Bool
isNamePerform n = n == namePerform 0 || n == namePerform 1 || n == namePerform 2 || n == namePerform 3 || n == namePerform 4

isNameClause :: Name -> Bool
isNameClause n =
  n == nameClause "tail" 0 || n == nameClause "tail" 1 || n == nameClause "tail" 2
  || n == nameClause "tail" 3 || n == nameClause "tail" 4 ||
  n == nameClause "control" 0 || n == nameClause "control" 1 || n == nameClause "control" 2
  || n == nameClause "control" 3 || n == nameClause "control" 4

isNameControl :: Name -> Bool
isNameControl n =
  n == nameClause "control" 0 || n == nameClause "control" 1 || n == nameClause "control" 2
  || n == nameClause "control" 3 || n == nameClause "control" 4

isNameTail :: Name -> Bool
isNameTail n =
  n == nameClause "tail" 0 || n == nameClause "tail" 1 || n == nameClause "tail" 2
  || n == nameClause "tail" 3 || n == nameClause "tail" 4

toClause :: Name -> AChange -> AChange
toClause n (AChangeClos clos env) = AChangeOp n clos env

performN :: Name -> Int
performN n
  | n == namePerform 0 = 0
  | n == namePerform 1 = 1
  | n == namePerform 2 = 2
  | n == namePerform 3 = 3
  | n == namePerform 4 = 4
  | otherwise = error "performN"

getTypeFromHandler :: Expr -> Effect
getTypeFromHandler (App (TypeApp (Con tn _) targs) hargs n) =
  case splitFunScheme (typeOf tn) of
    Just (_, _, targs, eff, res) -> 
      -- trace ("getTypeFromHandler: " ++ show res) $
      res
    Nothing -> error "getTypeFromHandler"

doStep :: HasCallStack => FixInput -> FixAAMR r s e FixChange
doStep i =
  memo i $ do
    analysisLog ("Step: " ++ show i)
    case i of
      Eval expr env store kstore lkont kont mkont time@(KTime tlabel contour) -> do
        let time' = 
              case lkont of
                [] -> time
                f:_ -> newTime time i Nothing
        -- trace ("Eval: " ++ showSimpleContext expr) $ do
        case exprOfCtx expr of
          Lit l -> doGC $ Cont (injLit l env) store kstore lkont kont mkont time'
          Var x _ -> do
            if isPrimitive x then do
              doGC $ Cont (AChangePrim x expr env) store kstore lkont kont mkont time'
            else do
              -- trace ("Var: " ++ show x ++ " " ++ show env) $ return ()
              -- trace ("Var: " ++ show (contextOf expr)) $ return ()
              v <- storeLookup x env store
              doGC $ Cont v store kstore lkont kont mkont time'
          Con _ _ -> do
            doGC $ Cont (AChangeConstr expr env) store kstore lkont kont mkont time'
          App (Var name _) (hnd:args) _ | isNameReset name -> do
            c <- focusChild 2 expr
            let tp = getTypeFromHandler hnd
            trace ("Reset: " ++ show tp) $ return ()
            -- trace ("Handle: " ++ show (vcat $ map (text . show) tps)) $ return ()
            doGC $ Eval c env store kstore [HandleL [] tp expr env,EndHandle] kont mkont time'
          
          App (Var name _) args _ | isNameShift name -> do
            select <- focusChild 2 expr
            let eff =
                  case contextOf <$> enclosingLambda expr of
                    Just (Just lam) -> case exprOfCtx lam of
                      Lam args eff body -> eff
                      _ -> error "doStep: Perform"
                n = performN $ getName name
            doGC $ Eval select env store kstore [OpL expr env n eff] kont mkont time'
          App f args _ -> do
            f <- focusChild 0 expr
            doGC $ Eval f env store kstore (AppL (length args) expr env:lkont) kont mkont time'
          Lam args eff body -> do
            doGC $ Cont (AChangeClos expr (limitEnv env (fvs expr))) store kstore lkont kont mkont time'
          TypeLam args body -> do
            doGC $ Cont (AChangeClos expr (limitEnv env (fvs expr))) store kstore lkont kont mkont time'
          TypeApp (TypeLam _ _) _ -> do
            -- trace ("TypeApp: " ++ showSimpleContext e) $ return () 
            doGC $ Cont (AChangeClos expr (limitEnv env (fvs expr))) store kstore lkont kont mkont time'
          TypeApp (Var _ _) _ -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store kstore lkont kont mkont time'
          TypeApp (Con _ _) _ -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store kstore lkont kont mkont time'
          Case [e] bs -> do
            ex <- focusChild 0 expr
            doGC $ Eval ex env store kstore (CaseR expr env:lkont) kont mkont time'
          Let binds body -> do
            ex <- focusChild 1 expr
            -- trace ("Let: " ++ show binds ++ showSimpleContext ex) $ return ()
            let bg = head binds
            addrs <- allocBindAddrs bg expr time
            let env' = extendEnv env (dgTNames bg) addrs
            doGC $ Eval ex env' store kstore (LetL 0 (length binds) 0 (length $ defsOf bg) addrs expr env':lkont) kont mkont time'
          _ -> error $ "doStep: " ++ show expr ++ " not handled"
      Cont achange store kstore lkont kont mkont time@(KTime tlabel contour) -> do
        -- trace ("Cont: " ++ show l ++ " " ++ show k) $ return ()
        let time' = 
              case lkont of
                [] -> time
                f:_ -> newTime time i (Just f)
        case lkont of
          [OpL expr env n eff] -> do
            let AChangeClos select senv = achange
            child <- focusChild 0 select
            doGC $ Eval child senv store kstore [OpL1 expr env n eff] kont mkont time'
          [OpL1 expr env n eff] -> do
            if n == 0 then do -- perform(s)(v..) ==> \v..,s -> Shift0 \k -> \h -> h(OpParams(s,fn(y) k(y)(h), v..)) -- There is a few places we can add v.. (we could apply it to k(y)(h)(v..))
              let AChangeClos lam env = achange
              -- trace ("OpL20: " ++ show body) $ return ()
              -- x <- newExpr (Lam ["k", "h", "s", "v"] typeTotal (App [Var "h" typeTotal], [Var "k" typeTotal, Var "h" typeTotal] typeTotal) typeTotal
              doGC $ Cont achange store kstore [Shift0k achange env 0 eff] kont mkont time'
            else do
              arg <- focusChild 3 expr
              doGC $ Eval arg env store kstore [OpL2 expr env n achange [] eff] kont mkont time'
          [OpL2 expr env n ch achanges eff] -> do
            if n == length achanges + 1 then do
              trace ("OpL2=l" ++ show n ++ ": " ++ show achange) $ return ()
              doGC $ Eval expr env store kstore [Shift0k achange env 0 eff] kont mkont time'
            else do
              -- trace ("OpL2: " ++ show (length achanges)) $ return ()
              arg <- focusChild (4 + length achanges) expr
              doGC $ Eval arg env store kstore [OpL2 expr env n ch (achanges ++ [achange]) eff] kont mkont time'
          [OpR expr changes eff ([hndframe@(HandleR [tag, hnd, ret, act] ef e p), EndHandle], kont', mkont')] -> do
            -- TODO: This has a problem of not returning to after calling resume to the operation body
            -- TODO: Write the math for algebraic effects + AAM
            -- trace ("OpR: " ++ show achange) $ return ()
            let AChangeOp nm op openv = achange
            opbod <- focusBody op -- TODO: Should the addresses of the allocations be based on the new time?
            let (names, addrs) = lamAddrs op time
            if isNameTail nm then do
              -- If reaching the continuation normally resume to kaddr, if searching for a handler lookup from above this handler
              let (env', store') = extend openv store names addrs changes
              doGC $ Eval opbod env' store' kstore [KResume,hndframe,EndHandle] kont mkont time'
            else if isNameControl nm then do
              -- trace ("Is Control" ++ show handlerframes) $ return ()
              -- Need to add continuation to the addrs & changes
              let addrs' = addrs ++ [(last names, contextId op, contour)]
                  changes' = changes ++ [AChangeKont kont mkont] --TODO: Add local , or rebind kont -- ensure this kont is right?
                  (env', store') = extend openv store names addrs' changes'
              doGC $ Eval opbod env' store' kstore [EndHandle] kont' mkont' time'
            else
              error "OpR"
          HandleR [tag, hnd, retClos, act] ef e p:ls -> do 
            -- (Eval body) [Cont AppR retClos, EndHandle] 
            --    [OpMatch (\o -> 
            --        case o of OpParams(s,v,k) && o in hnd -> s(hnd)(v,k)
            --             OpParams(s,v,k) -> Shift0 \k' -> \h -> h(OpParams(s,v,fn(y) k'(k(y,h))))
            --        
            --     ]:mkont)
            -- trace ("HandleR: " ++ show (length [tag, hnd, retClos, act])) $ return ()
            let AChangeClos ret env = retClos
                (names, addrs) = lamAddrs ret time
                (env', store') = extend env store [head names] [head addrs] [achange]
            body <- focusBody ret
            doGC $ Eval body env' store' kstore ls kont mkont time'
          HandleL changes ef e p:ls -> do -- TODO: Time?
            trace ("HandleL: " ++ show (length changes) ++ show changes) $ return ()
            if length changes == 2 then do
              let AChangeClos lam env = head changes
              body <- focusBody lam
              let kaddr = KAddr (lam, env, contour)
              let mkaddr = MKAddr (lam, env, contour)
              let kstore' = kstoreExtend kaddr (HandleR (changes ++ [achange]) ef e p:ls) kont kstore
              let mkstore' = mkstoreExtend mkaddr (HandleR (changes ++ [achange]) ef e p:ls) kont mkont kstore'
              trace ("Evaluating action body" ++ show body) $ return ()
              doGC $ Eval body env store mkstore' [EndCall] kaddr mkaddr time'
            else do
              nextparam <- focusChild (length changes + 2) e
              doGC $ Eval nextparam p store kstore (HandleL (changes ++ [achange]) ef e p:ls) kont mkont time'
          l@(AppL n e p):ls -> do
            if n == 0 then do
              let AChangeClos lam env = achange
              body <- focusBody lam
              let kaddr = KAddr (lam, env, contour)
              doGC $ Eval body env store (kstoreExtend kaddr ls kont kstore) [EndCall] kaddr mkont time'
            else if n == 1 then do
              arge <- focusChild 1 e
              addrs <- alloc i l
              -- trace ("AppL: " ++ show n ++ " " ++ show arge ++ " " ++ show p) $ return ()
              -- k' <- 
              doGC $ Eval arge p store kstore (AppR achange addrs e:ls) kont mkont time'
            else do
              arge <- focusChild 1 e
              -- trace ("AppL: " ++ show n ++ " " ++ show arge ++ " " ++ show p) $ return ()
              addrs <- alloc i l
              doGC $ Eval arge p store kstore (AppM achange addrs e 1 n p:ls) kont mkont time'
          AppM clos addrs e n t p:ls -> do
            arge <- focusChild (n + 1) e
            -- trace ("AppM: " ++ show n ++ " " ++ show arge ++ " " ++ show clos) $ return ()
            let store' = extendStore store (addrs !! (n - 1)) achange
            if n + 1 == t then do
              -- trace ("AppRM: " ++ show clos) $ return ()
              doGC $ Eval arge p store' kstore (AppR clos addrs e:ls) kont mkont time'
            else do
              doGC $ Eval arge p store' kstore (AppM clos addrs e (n + 1) t p:ls) kont mkont time'
          (AppR c@(AChangePrim p clos env) addrs e):ls | isNameClause (getName p) -> do
            trace ("ClauseTail: " ++ show c ++ " " ++ show ls) $ return ()
            doGC $ Cont (toClause (getName p) achange) store kstore ls kont mkont time'
          (AppR c@(AChangeKont k mk) addrs e):ls -> do
            trace ("Call resume:" ++ show k) $ return ()
            case M.lookup k (fst kstore) of
              Just sframes -> do
                (frames, retKont) <- each $ map return (S.toList sframes) -- TODO: GC the kstore prior to extending it
                doGC $ Cont achange store kstore frames retKont mk time'
          (AppR c@(AChangeClos lam env) addrs e):ls -> do
            trace ("AppR: " ++ show c ++ " " ++ show ls) $ return ()
            body <- focusBody lam
            let args = lamArgNames lam
                store' = extendStore store (last addrs) achange
                kaddr = KAddr (lam, env, contour)
            -- trace ("AppR: " ++ show c ++ " " ++ show ls) $ return ()
            doGC $ Eval body (extendEnv env args addrs) store' (kstoreExtend kaddr ls kont kstore) [EndCall] kaddr mkont time'
          (AppR ccon@(AChangeConstr con env) addrs e):ls -> do
            case exprOfCtx con of
              Con _ _ -> do
                let store' = extendStore store (last addrs) achange
                    env' = M.fromList (zip (tnamesCons (length addrs)) addrs)
                -- trace ("AppRCon: " ++ show con ++ " " ++ show env' ++ " " ++ show addrs) $ return ()
                -- trace ("AppRCon:\n" ++ showStore store) $ return ()
                doGC $ Cont (AChangeConstr con env') store' kstore ls kont mkont time'
          (AppR cprim@(AChangePrim p ctx env) addrs e):ls -> do
            trace ("Prim store " ++ showStore store) $ return ()
            let store' = extendStore store (last addrs) achange
            res <- doPrimitive (getName p) addrs env store'
            -- trace ("Primitive Result " ++ show cprim ++ " " ++ show res ++ " " ++ show ls) $ return ()
            doGC $ Cont res store' kstore ls kont mkont time'
          LetL bgi bgn bi bn addrs e p:ls -> do
            let dgs = letDefsOf e
                store' = extendStore store (addrs !! bi) achange
            -- trace ("LetL: " ++ show bgi ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ show addrs) $ return ()
            if bgi + 1 == bgn && bi + 1 == bn then do
              -- trace ("LetL End") $ return ()
              body <- focusChild 0 e
              doGC $ Eval body (extendEnv p (dgsTNames dgs) addrs) store' kstore ls kont mkont time'
            else if bi + 1 /= bn then do
              -- trace ("LetL In Group") $ return ()
              bind <- focusLetDefBinding bgi bi e
              doGC $ Eval bind p store' kstore (LetL bgi bgn (bi + 1) bn addrs e p:ls) kont mkont time'
            else if bi + 1 == bn then do
              -- trace ("LetL End Group") $ return ()
              let bgi' = bgi + 1
                  bg = dgs !! bgi'
              bind <- focusLetDefBinding bgi' bi e
              addrs' <- allocBindAddrs bg e time
              let env' = extendEnv p (dgTNames bg) addrs'
              doGC $ Eval bind env' store' kstore (LetL bgi' bgn 0 (length $ defsOf bg) addrs' e p:ls) kont mkont time'
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
                    -- trace ("MatchChange: " ++ show achange) $ return ()
                    -- trace ("MatchStore:\n" ++ showStore store) $ return ()
                    matches <- matchBindPattern achange pat env store (S.unions $ map (localFv . guardExpr) body)
                    case matches of
                      Just (venv, vstore) -> do
                        body <- focusChild n expr
                        let free = fvs body
                        -- trace ("Match: " ++ show pat ++ " " ++ show venv ++ "\n") $ return ()
                        -- trace ("Body: " ++ show body) $ return ()
                        doGC $ Eval body venv vstore kstore ls kont mkont time'
                      Nothing -> matchBranches achange bs
                  matchBindPattern :: HasCallStack => AChange -> Pattern -> VEnv -> VStore -> S.Set TName -> FixAAMR r s e (Maybe (VEnv, VStore))
                  matchBindPattern achange pat venv vstore tnames = do
                    case pat of
                      PatWild -> return $ Just (venv, vstore)
                      PatVar x pat' -> do
                        let addr = (x, contextId expr, contour)
                            env' = M.insert x addr venv
                        -- trace ("MatchX: " ++ show x ++ " " ++ show addr ++ " " ++ show env') $ return ()
                        -- trace ("MatchX: \n" ++ showStore vstore) $ return ()
                        matchBindPattern achange pat' env' (extendStore vstore addr achange) tnames
                      PatCon con pats _ _ _ _ _ skip -> do
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
                                      matchBindPattern v pat venv vstore tnames
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
          [EndCall] -> do
            (l, k, mk) <- pop lkont kont mkont kstore
            doGC $ Cont achange store kstore l k mk time'
          [EndHandle] -> do
            (l, k, mk) <- pop lkont kont mkont kstore
            doGC $ Cont achange store kstore l k mk time'
          KResume:handlerframes -> do -- Handler frames are kept to have the right handler stack for searching -- probably not needed with meta kont
            let res = M.lookup kont (fst kstore)
            (l, k) <- each $ map return (maybe [] S.toList res)
            doGC $ Cont achange store kstore l k mkont time'
          [EndProgram] ->
            return $ AC achange
          [] -> do
            (l, k, mk) <- pop lkont kont mkont kstore
            doGC $ Cont achange store kstore l k mk time
          _ -> error $ "doStep: " ++ show lkont


pop :: HasCallStack => [Frame] -> KAddr -> MKAddr -> KStore -> FixAAMR r s e ([Frame], KAddr, MKAddr)
pop lkont kont mkont kstore =
  case lkont of
    [] ->
      case kont of
        KEnd ->
          case mkont of
            MKEnd -> return ([], kont, mkont)
            _ ->
              case M.lookup mkont (snd kstore) of
                Just mkonts -> do
                  each (map return (S.toList mkonts))
                Nothing -> error "pop: Not found"
        _ ->
          case M.lookup kont (fst kstore) of
            Just konts -> do
              each (map (\(l, k) -> return (l, k, mkont)) (S.toList konts))
            Nothing -> error "pop: Not found"
    f:ls -> return (ls, kont, mkont)

doGC :: FixInput -> FixAAMR r s e FixChange
doGC i = do
  i' <- gc i
  doStep i'

-- TODO: Delimited Control