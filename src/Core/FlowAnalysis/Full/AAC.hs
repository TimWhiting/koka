{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.AAC where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.AbstractValue
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
import Core.FlowAnalysis.Demand.AbstractValue (LiteralChange(..))
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)

type VStore = M.Map Addr AbValue
data FixInput =
  Eval ExprContext VEnv VStore KClos LocalKont (Maybe Kont) (Maybe MetaKont)
  | Cont LocalKont (Maybe Kont) (Maybe MetaKont) AChange VStore KClos
  | KStoreGet ExactContext
  | CStoreGet MetaKont
  | Pop LocalKont (Maybe Kont)
  | NoTop LocalKont (Maybe Kont)
  deriving (Eq, Ord)

data FixOutput a =
  A AbValue
  | K (S.Set (LocalKont, Maybe Kont))
  | C (S.Set (LocalKont, Maybe Kont, Maybe MetaKont))
  | B (S.Set Bool)
  | Bottom
  deriving (Eq, Ord)

data FixChange =
  AC AChange
  | KC LocalKont (Maybe Kont)
  | CC LocalKont (Maybe Kont) (Maybe MetaKont)
  | BC Bool
  | ChangeBottom
  deriving (Eq, Ord)

type FixAACR r s e a = FixAR r s e FixInput FixOutput FixChange a
type FixAAC r s e = FixAACR r s e (FixOutput FixChange)
type PostFixAACR r s e a = PostFixAR r s e FixInput FixOutput FixChange a
type PostFixAAC r s e = PostFixAACR r s e (FixOutput FixChange)

data Frame =
  End
  | AppL Int ExprContext VEnv -- Length of args and parent expression
  | AppM AChange [Addr] ExprContext Int Int VEnv -- This environment is the one in which the args are evaluated
  | AppR AChange [Addr]
  | LetL Int Int Int Int [Addr] ExprContext VEnv -- Binding group index, num binding groups, binding index, num bindings, addresses for binding group, parent expresion, parent env
  | CaseR ExprContext VEnv
  deriving (Eq, Ord)

instance Show Frame where
  show End = "End"
  show (AppL nargs e p) = "AppL " ++ show nargs ++ " " ++ showSimpleEnv p
  show (AppM ch chs e n t p) = "AppL " ++ show n ++ " " ++ show t
  show (AppR ch chs) = "AppR " ++ show ch ++ " " ++ show chs
  show (CaseR e p) = "CaseR"
  show (LetL bgi bgn bi bn addrs e p) = "LetL " ++ show bgi ++ " " ++ show bgn ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ showSimpleContext e ++ " " ++ showSimpleEnv p

type LocalKont = [Frame]

type ApproxContext = (ExprContext, VEnv, Addr)
type ExactContext = (ExprContext, VEnv, VStore, KClos)
data Kont =
  MPrecise ExactContext
  | MApprox ApproxContext
  deriving (Eq, Ord, Show)

data KontA =
  KApprox LocalKont ApproxContext
  | KExact LocalKont
  deriving (Eq, Ord, Show)

type KClos = M.Map Addr (S.Set VStore)
data MetaKont =
  MReset ExprContext VEnv VStore KClos
  | MApply KontA AChange VStore KClos
  deriving (Eq, Ord, Show)


eachValue :: (Ord i, Show d, Show (l d), Lattice l d) => AbValue -> FixT e s i l d AChange
eachValue ab = each $ map return (changes ab)

storeUpdate :: VStore -> [(TName,Int)] -> [AChange] -> VStore
storeUpdate store [] [] = store
storeUpdate store (i:is) (v:vs) =
  let updated = M.alter (\oldv -> case oldv of {Nothing -> Just (addChange emptyAbValue v); Just ab -> Just (addChange ab v)}) i store
  in storeUpdate updated is vs
storeUpdate _ a b = error $ "storeUpdate\n" ++ show a ++ "\n" ++ show b ++ "\n"

limitEnv :: VEnv -> S.Set TName -> VEnv
limitEnv env fvs = M.filterWithKey (\k _ -> k `S.member` fvs) env

extendEnv :: VEnv -> [TName] -> [(TName,Int)] -> VEnv
extendEnv env args addrs = M.union (M.fromList $ zip args addrs) env -- Left biased will take the new

-- 0CFA Allocation
alloc :: HasCallStack => FixInput -> LocalKont -> FixAACR r s e [Addr]
alloc (Cont _ _ _ (AChangeClos lam env) store xclos) (AppL nargs e env':ls) = do
  let names = lamArgNames lam
  if length names /= nargs then error ("alloc: " ++ show names ++ " " ++ show nargs)
  else do
    let addrs = [0..length names]
    return $ zip names addrs
alloc (Cont _ _ _ (AChangeConstr con env) store xclos) (AppL nargs e env':ls) = do
  case exprOfCtx con of
    Con tn _ -> do
      let addrs = [0..nargs]
          tp = typeOf tn
      case splitFunType tp of
        Just (args, _, _) -> return $ zip (map (\(n,t) -> TName n t Nothing) args) addrs
        Nothing -> return [(tn, 0)]

allocBindAddrs :: HasCallStack => DefGroup -> FixAACR r s e [Addr]
allocBindAddrs (DefRec defs) = do
  let names = dfsTNames defs
  return $ zip names [0..]
allocBindAddrs (DefNonRec df) = return [(TName (defName df) (defType df) Nothing, 0)]

tnamesCons :: Int -> [TName]
tnamesCons n = map (\i -> TName (newName ("con" ++ show i)) typeAny Nothing) [0..n]

doStep :: HasCallStack => FixInput -> FixAACR r s e FixChange
doStep i = do
  memo i $ do
    trace ("Step: " ++ show i) $ return ()
    case i of
      Eval expr env store xclos local kont meta ->
        -- trace ("Eval: " ++ showSimpleContext expr) $ do
        case exprOfCtx expr of
          Lit l -> return $ AC $ injLit l env
          Var x _ -> do
            let maddr  = M.lookup x env
            case maddr of
              Just addr -> do
                let value = store M.! addr
                v <- eachValue value
                doStep $ Cont local kont meta v store xclos
              Nothing -> do
                mdef <- bindExternal x
                case mdef of
                  Nothing -> doBottom
                  Just def -> do
                    lam <- focusChild 0 def
                    doStep $ Cont local kont meta (AChangeClos lam M.empty) store xclos
          Con _ _ -> do
            doStep $ Cont local kont meta (AChangeConstr expr env) store xclos
          App (TypeApp (Var name _) _) args _ | nameEffectOpen == getName name -> do
            f <- focusChild 1 expr
            doStep $ Eval f env store xclos (AppL (length args) expr (limitEnv env (fvs expr)) : local) kont meta
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
            addrs <- allocBindAddrs bg
            doStep $ Eval ex (extendEnv env (dgTNames bg) addrs) store xclos (LetL 0 (length binds) 0 (length $ defsOf bg) addrs expr env : local) kont meta
          _ -> error $ "doStep: " ++ show expr ++ " not handled"
      Cont [] Nothing Nothing achange store xclos -> return $ AC achange
      Cont [] kont meta achange store xclos -> do
        (error "Cont []") -- TODO: Approximate
        -- Need no-top?
        doBottom
      Cont lc kont meta achange store xclos -> do
        KC l k <- doStep (Pop lc kont)
        case l of
          AppL n e p:ls -> do
            let AChangeClos lam env = achange
            arge <- focusChild n e
            if n == 0 then doStep $ Eval arge p store xclos (AppR achange []:ls) k meta
            else do
              addrs <- alloc i l
              doStep $ Eval arge p store xclos (AppM achange addrs e 1 n p:ls) k meta
          AppM clos addrs e n t p:ls -> do
            arge <- focusChild n e
            let store' = storeUpdate store [addrs !! (n - 1)] [achange]
            if n == t then doStep $ Eval arge p store' xclos (AppR clos addrs:ls) k meta
            else doStep $ Eval arge p store' xclos (AppM clos addrs e (n + 1) t p:ls) k meta
          (AppR (AChangeClos clos env) addrs):ls -> do
            body <- focusBody clos
            let args = lamArgNames clos
            doStep $ Eval body (extendEnv env args addrs) store xclos [] k meta
          (AppR ccon@(AChangeConstr con env) addrs):ls -> do
            case exprOfCtx con of
              Con _ _ -> do
                doStep $ Cont l k meta (AChangeConstr con (M.fromList (zip (tnamesCons (length addrs)) addrs))) store xclos
          LetL bgi bgn bi bn addrs e p:ls -> do 
            let dgs = letDefsOf e
            -- trace ("LetL: " ++ show bgi ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ show addrs) $ return ()
            let store' = storeUpdate store [addrs !! bi] [achange]
            if bgi + 1 == bgn && bi + 1 == bn then do
              -- trace ("LetL End") $ return ()
              body <- focusChild 0 e
              doStep $ Eval body (extendEnv p (dgsTNames dgs) addrs) store' xclos ls k meta
            else if bi + 1 /= bn then do
              -- trace ("LetL In Group") $ return ()
              bind <- focusLetDefBinding bgi bi e
              doStep $ Eval bind p store' xclos (LetL bgi bgn (bi + 1) bn addrs e p:ls) k meta
            else if bi + 1 == bn then do
              -- trace ("LetL End Group") $ return ()
              let bgi' = bgi + 1
              let bg = dgs !! bgi'
              bind <- focusLetDefBinding bgi' bi e
              addrs <- allocBindAddrs bg
              doStep $ Eval bind (extendEnv p (dgTNames bg) addrs) store' xclos (LetL bgi' bgn 0 (length $ defsOf bg) addrs e p:ls) k meta
            else
              error "Cont LetL"
          (CaseR expr env): ls -> do
            case exprOfCtx expr of
              Case [e] bs -> do
                matchBranches achange (zip bs [1..])
                where
                  matchBranches :: AChange -> [(Branch, Int)] -> FixAACR r s e FixChange
                  matchBranches achange [] = doBottom
                  matchBranches achange ((Branch [pat] body, n):bs) = do
                    matches <- matchBindPattern achange pat env store
                    case matches of
                      Just (venv, vstore) -> do
                        body <- focusChild n expr
                        let free = fvs body `S.difference` bv pat
                        doStep $ Eval body (limitEnv venv free) vstore xclos [] k meta
                      Nothing -> matchBranches achange bs
                  matchBindPattern :: AChange -> Pattern -> VEnv -> VStore -> FixAACR r s e (Maybe (VEnv, VStore))
                  matchBindPattern achange pat venv vstore = do
                    case pat of
                      PatWild -> return $ Just (venv, vstore)
                      PatVar x pat' ->
                        let addr = (x, 0)
                            env' = M.insert x addr env
                        in matchBindPattern achange pat' env' (storeUpdate vstore [addr] [achange])
                      PatCon _ pats _ _ _ _ _ _ -> do
                        foldM (\isMatch (pat, i) -> do
                            case isMatch of
                              Just (venv, vstore) -> do
                                case achange of 
                                  AChangeConstr acon aenv -> do
                                    let maddr  = M.lookup (TName (newName $ "con" ++ show i) typeAny Nothing) aenv
                                    case maddr of
                                      Just addr -> do
                                        let value = store M.! addr
                                        v <- eachValue value
                                        matchBindPattern v pat venv vstore
                                      _ -> error ("matchBindPattern: " ++ show pat ++ " " ++ show achange)
                                  _ -> return Nothing
                              Nothing -> return Nothing
                          ) (Just (venv, vstore)) (zip pats [0..])
                      PatLit x ->
                        case (x, achange) of
                          (LitInt i, AChangeLit (LiteralChangeInt (LChangeSingle i2)) _) -> if i == i2 then return (Just (venv, vstore)) else doBottom
                          (LitFloat f, AChangeLit (LiteralChangeFloat (LChangeSingle f2)) _) -> if f == f2 then return (Just (venv, vstore)) else doBottom
                          (LitChar c, AChangeLit (LiteralChangeChar (LChangeSingle c2)) _) -> if c == c2 then return (Just (venv, vstore)) else doBottom
                          (LitString s, AChangeLit (LiteralChangeString (LChangeSingle s2)) _) -> if s == s2 then return (Just (venv, vstore)) else doBottom
                          (LitInt i, AChangeLit (LiteralChangeInt LChangeTop) _) -> return (Just (venv, vstore)) -- TODO: Also evaluate other branches
                          (LitFloat f, AChangeLit (LiteralChangeFloat LChangeTop) _) -> return (Just (venv, vstore))
                          (LitChar c, AChangeLit (LiteralChangeChar LChangeTop) _) -> return (Just (venv, vstore))
                          (LitString s, AChangeLit (LiteralChangeString LChangeTop) _) -> return (Just (venv, vstore))
                          _ -> doBottom
              _ -> error "Cont CaseR"
      KStoreGet ctx -> doBottom
      CStoreGet meta -> doBottom
      Pop (l:ls) kont -> return $ KC (l:ls) kont
      Pop [] Nothing -> return $ KC [] Nothing
      Pop [] (Just (MPrecise ctx)) -> do
        KC l k <- doStep $ KStoreGet ctx
        doStep $ Pop l k
      -- Pop [] (Just approx@KApprox ctx) = do
      --   precise <- forT ctx
      --   doStep (Pop l k)
      NoTop [] Nothing -> return $ BC True
      NoTop (l:ls) k -> return $ BC False
      NoTop [] k -> do
        KC l k <- doStep (Pop [] k)
        doStep $ NoTop l k -- TODO: can we assume no new values get added & get a set and use (or)

approximate :: Addr -> KClos -> LocalKont -> Maybe Kont -> (KClos, KontA)
approximate a x l Nothing = (x, KExact l)
approximate a x l (Just (MPrecise (f, v, st, x1))) = ((x `unionK` x1) `unionK` M.singleton a (S.singleton st), KApprox l (f, v, a))
approximate a x l (Just (MApprox (f, v, b))) = let Just !xx = M.lookup b x in (x, KApprox l (f, v, a))

unionK :: KClos -> KClos -> KClos
unionK = M.unionWith S.union

addKont :: ExactContext -> LocalKont -> Maybe Kont -> FixAACR r s e ()
addKont c lk mk = lift $ push (KStoreGet c) (KC lk mk)

addMetaKont :: MetaKont -> LocalKont -> Maybe Kont -> Maybe MetaKont -> FixAACR r s e ()
addMetaKont c lk mk mmk = lift $ push (CStoreGet c) (CC lk mk mmk)

-- forKont :: KClos -> ExprContext -> VEnv -> Addr -> FixAACR r s e ExactContext
-- forKont kclos expr venv a = do
--   let store = kclos M.! a
--   doStep (KStoreGet )
-- Actually need to introspect the full KStore....

instance Show (FixOutput a) where
  show (A x) = show x
  show (K x) = show x
  show (C x) = show x
  show (B x) = show x
  show Bottom = "Bottom"

instance Show FixChange where
  show (AC x) = show x
  show (KC l k) = show l ++ " " ++ show k
  show (CC l k c) = show l ++ " " ++ show k ++ " " ++ show c
  show (BC b) = show b
  show ChangeBottom = "Bottom"

instance Show FixInput where
  show (Eval expr env store kclos local kont meta) = "Eval " ++ showSimpleContext expr ++ " " ++ showSimpleEnv env
  show (Cont local kont meta achange store kclos) = "Cont " ++ show local ++ " " ++ show kont ++ " " ++ show meta ++ " " ++ show achange
  show (KStoreGet ctx) = "KStoreGet"
  show (CStoreGet meta) = "CStoreGet"
  show (Pop local kont) = "Pop"
  show (NoTop local kont) = "NoTop"

instance Lattice FixOutput FixChange where
  bottom = Bottom
  isBottom Bottom = True
  isBottom _ = False
  insert (AC a) Bottom = A $ addChange emptyAbValue a
  insert (AC a) (A x) = A $ addChange x a
  insert (KC l k) (K x) = K $ S.insert (l, k) x
  insert (KC l k) Bottom = K $ S.singleton (l, k)
  insert (CC l k c) (C x) = C $ S.insert (l, k, c) x
  insert (CC l k c) Bottom = C $ S.singleton (l, k, c)
  insert (BC b) (B x) = B $ S.insert b x
  insert (BC b) Bottom = B $ S.singleton b
  insert ChangeBottom a = a
  join Bottom Bottom = Bottom
  join Bottom x = x
  join x Bottom = x
  join (A x) (A y) = A (joinAbValue x y)
  join (K x) (K y) = K (S.union x y)
  join (C x) (C y) = C (S.union x y)
  join (B x) (B y) = B (S.union x y)
  lte ChangeBottom _ = True
  lte _ Bottom = False
  lte (CC l k c) (C y) = (l, k, c) `S.member` y
  lte (KC l k) (K y) = (l, k) `S.member` y
  lte (AC x) (A y) = x `changeIn` y
  lte (BC x) (B y) = x `elem` y
  lte x y = error ("lte: " ++ show x ++ " " ++ show y)
  elems (A a) = map AC $ changes a
  elems (K x) = map (uncurry KC) $ S.toList x
  elems (C x) = map (\(l,k,c) -> CC l k c) $ S.toList x
  elems (B x) = map BC $ S.toList x
  elems Bottom = []



