module Core.FlowAnalysis.Full.AAM.DelimitedTransform(
  isNameReset, 
  isNameShift, 
  delimitedControlTransformDefs) where

import qualified Lib.Trace
import Control.Monad
import Control.Monad.Identity
import Control.Applicative
import Data.Maybe( catMaybes, isJust, maybeToList, isNothing, fromJust, fromMaybe )
import Lib.PPrint
import Common.Failure
import Common.NamePrim ( nameEffectOpen, namePatternMatchError, namePerform, nameHandle )
import Common.Name
import Common.Range
import Common.Unique
import Common.Error
import Common.Syntax

import Kind.Kind
import Type.Type
import Type.Kind
import Type.TypeVar
import Type.Pretty hiding (Env)
import qualified Type.Pretty as Pretty
import Type.Assumption
import Core.Core
import qualified Core.Core as Core
import Core.Pretty
import Core.CoreVar
import Core.Uniquefy
import Data.List (intercalate)
import qualified Data.Set as S

trace s x =
  Lib.Trace.trace s
    x

delimitedControlTransformDefs :: CorePhase b ()
delimitedControlTransformDefs
  = liftCorePhaseUniq $ \uniq defs ->
    runUnique uniq $ delimitedControlTransformDefGroups defs

{--------------------------------------------------------------------------
  transform definition groups
--------------------------------------------------------------------------}
delimitedControlTransformDefGroups :: DefGroups -> Unique DefGroups
delimitedControlTransformDefGroups
  = mapM delimitedControlTransformDefGroup

delimitedControlTransformDefGroup :: DefGroup -> Unique DefGroup
delimitedControlTransformDefGroup (DefRec dgs)
  = do ndgs <- mapM delimitedControlTransformRecDef dgs
       return $ DefRec ndgs
delimitedControlTransformDefGroup (DefNonRec def)
 = do ndef <- delimitedControlTransformRecDef def
      return $ DefNonRec ndef

delimitedControlTransformRecDef :: Def -> Unique Def
delimitedControlTransformRecDef def
  = -- rewrite expressions using delimitedControlTransformExpr
    do e <- rewriteBottomUpM delimitedControlTransformExpr $ defExpr def
      --  trace ("Transformed: " ++ show e) $ return ()
       return def{defExpr=e}

isNamePerform :: Name -> Bool
isNamePerform n = n == namePerform 0 || n == namePerform 1 || n == namePerform 2 || n == namePerform 3 || n == namePerform 4

performN :: Name -> Int
performN n
  | n == namePerform 0 = 0
  | n == namePerform 1 = 1
  | n == namePerform 2 = 2
  | n == namePerform 3 = 3
  | n == namePerform 4 = 4
  | otherwise = error "performN"

nshift0 = newName "shift0"
shift0 = TName nshift0 typeTotal Nothing
varshift0 = Var shift0 InfoNone
nreset = newName "reset$"
resetdollar = TName nreset typeTotal Nothing
varResetDollar = Var resetdollar InfoNone

isNameReset :: TName -> Bool
isNameReset n = getName n == nreset

isNameShift n = getName n == nshift0

tnk = TName (newName "k") typeTotal Nothing
vark = Var tnk InfoNone

tnh = TName (newName "h") typeTotal Nothing
varh = Var tnh InfoNone

tns = TName (newName "s") typeTotal Nothing
tnv i = TName (newName ("v" ++ show i)) typeTotal Nothing
tny = TName (newName "y") typeTotal Nothing
tnx = TName (newName "x") typeTotal Nothing
s = Var tns InfoNone
vn i = Var (tnv i) InfoNone
y = Var tny InfoNone
x = Var tnx InfoNone

opn = TName (newName "op") typeTotal Nothing
opv = Var opn InfoNone

runop = TName (newName "runop") typeTotal Nothing
varrunop = Var runop InfoNone

opConName = TName (newName "OpParams") typeTotal Nothing

opConRepr = ConSingleton (newName "xx") DataSingleStruct valueReprZero (-1)

tnSelect = TName (newName "select") typeAny Nothing
tnKont = TName (newName "kont") typeAny Nothing
tnVars v = TName (newName $ "v" ++ show v) typeAny Nothing

vSelect = Var tnSelect InfoNone
vKont = Var tnKont InfoNone

conInfo :: ConInfo
conInfo = ConInfo (newName "xx") (newName "xx") [] [] [] typeAny Inductive rangeNull [] [] False [] valueReprZero Private ""

delimitedControlTransformExpr :: Expr -> Unique Expr
delimitedControlTransformExpr body =
    -- trace ("Transforming: " ++ show body) $ do
    case body of
-- perform(s)(v..) ==> \v..,s -> Shift0 \k -> \h -> h(OpParams(s,fn(y) k(y)(h), v..)) -- There is a few places we can add v.. (we could apply it to k(y)(h)(v..))
      App (TypeApp (Var tn _) tps) (idx:select:args) rng | isNamePerform $ getName tn -> do
        trace ("Perform: " ++ show (map (ppType defaultEnv) tps)) $ return ()
        case splitFunScheme (typeOf tn) of
          Just (_, _, _, eff, ret) ->  trace ("Perform: " ++ show eff) $ return ()
        let nargs = performN $ getName tn
        let argsVars = [vn i | i <- [0..nargs-1]]
        let argNms = [tnv i | i <- [0..nargs-1]]
        return $ App (Lam argNms typeTotal
                    $ App varshift0 [
                      Lam [tnk] typeTotal $
                        Lam [tnh] typeTotal $
                          App varh [
                              App (Con opConName opConRepr)
                                 ([select, Lam [tny] typeTotal (App (App vark [y] Nothing) [varh] Nothing)] ++ argsVars) Nothing
                                ] Nothing
                        ] rng) args Nothing
      App (TypeApp (Var name _) _) [f] _ | nameEffectOpen == getName name -> do
        return f
-- TODO: Specialize for no continuation also in perform / propagate
-- Handle hnd e_body x.e_return ==>
--   let h_x = \o -> runop(o) -- runop is primitive
--        OpParams(s,k,v..) -> s(hnd)(v..,k)
--        OpParams(s,k,v..) -> Shift0 \k' -> \h' -> h'(OpParams(s,fn(y) k(k'(y)(h')), v..))
--   <e_body|\(x,h) -> e_return>(h_x) -- <|> is primitive
      App (TypeApp (Var name _) tps) [hnd, Lam [tnx] _ retfn, action] _ | isHandleName (getName name) -> do
        trace ("Handle: " ++ show tps) $ return ()
        let pselect = PatVar tnSelect PatWild
            pk = PatVar tnKont PatWild
        let hx = Lam [opn] typeTotal $
                  Case [App varrunop [opv] Nothing]
                    [
                      Branch [PatCon opConName [pselect, pk] opConRepr [] [] typeAny conInfo False]
                        [Guard exprTrue (App (App vSelect [hnd] Nothing) [vKont] Nothing)],
                      Branch [PatCon opConName [pselect, pk] opConRepr [] [] typeAny conInfo False]
                        [Guard exprTrue (App varshift0 [
                          Lam [tnk] typeTotal $
                            Lam [tnh] typeTotal $
                              App varh [
                                App (Con opConName opConRepr)
                                 ([vSelect, Lam [tny] typeTotal
                                 (App vKont [App (App vark [y] Nothing) [varh] Nothing] Nothing)]) Nothing
                              ] Nothing
                            ] Nothing)
                          ]
                    ]
        let res = App (App varResetDollar [hnd, action, Lam [tnx] typeTotal $ Lam [tnh] typeTotal retfn] Nothing) [hx] Nothing
        -- trace (show res) $ return ()
        return res
      _ -> return body
