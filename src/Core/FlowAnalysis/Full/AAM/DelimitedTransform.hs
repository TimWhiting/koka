module Core.FlowAnalysis.Full.AAM.DelimitedTransform(delimitedControlTransformDefs) where

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

shift0 = TName (newName "shift0") typeTotal Nothing
varshift0 :: Expr
varshift0 = Var shift0 InfoNone
tnk = TName (newName "k") typeTotal Nothing
vark = Var tnk InfoNone

tnh = TName (newName "h") typeTotal Nothing
varh = Var tnh InfoNone

tns = TName (newName "s") typeTotal Nothing
tnv i = TName (newName ("v" ++ show i)) typeTotal Nothing
tny = TName (newName "y") typeTotal Nothing
s = Var tns InfoNone
vn i = Var (tnv i) InfoNone
y = Var tny InfoNone

opConName = TName (newName "OpParams") typeTotal Nothing

delimitedControlTransformExpr :: Expr -> Unique Expr
delimitedControlTransformExpr body
  = case body of
-- perform(s)(v) ==> \v,s -> Shift0 \k -> \h -> h(OpParams(v,s,fn(y) k(y,h)))
      App (TypeApp (Var name _) _) (idx:TypeLam targs select:args) rng | isNamePerform $ getName name -> do
        trace ("Perform: " ++ show (vcat $ map (text . show) targs)) $ return ()
        let nargs = performN $ getName name
        let argsVars = [vn i | i <- [0..nargs-1]]
        let argNms = [tnv i | i <- [0..nargs-1]]
        return $ App (Lam argNms typeTotal
                    $ App varshift0 [
                      Lam [tnk] typeTotal $
                        Lam [tnh] typeTotal $
                          App varh [
                              App (Con opConName (ConSingleton (newName "xx") DataSingleStruct valueReprZero (-1)))
                                 ([select, Lam [tny] typeTotal (App vark [y,varh] Nothing)] ++ argsVars) Nothing
                                ] Nothing
                        ] rng) args Nothing
--TODO: Handle hnd e_body x.e_return ==>
--   let h_x = \o -> runop(o) -- runop is primitive
--        OpParams(s,v,k) -> s(hnd)(v,k)
--        OpParams(s,v,k) -> Shift0 \k' -> \h -> h(OpParams(s,v,fn(y) k'(k(y,h))))
--   <e_body|\(x,h) -> e_return>(h_x) -- <|> is primitive
      App (TypeApp (Var name _) tps@[_, _, tp, _, _]) args _ | nameHandle == getName name -> do
        trace ("Handle: " ++ show (vcat $ map (text . show) tps)) $ return ()
        return body
      _ -> return body
