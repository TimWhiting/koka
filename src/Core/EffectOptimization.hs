module Core.EffectOptimization(
                          
                        ) where

import Control.Monad hiding (join)
import Data.Set as S hiding (findIndex, filter, map)
import qualified Data.Sequence as Seq
import qualified Data.Map.Strict as M
import Common.Name
import Lib.PPrint
import Type.Pretty as Pretty
import Debug.Trace
import Core.Core as C
import Core.Monadic
import Common.Unique
import Core.StaticContext
import Core.AbstractValue
import Core.FixpointMonad
import Core.DemandAnalysis
import Compiler.Module
import Data.Maybe (fromMaybe)


--------------------------------------------------------------------------
-- Linear Effect Optimization
--------------------------------------------------------------------------
linearEffectOptimize :: Loaded -> Pretty.Env -> CorePhase () ()
linearEffectOptimize loaded penv
  = liftCorePhaseUniq $ \uniq defs -> 
    runUnique uniq (linearEffectOptimize' loaded penv defs)

linearEffectOptimize' :: Loaded -> Pretty.Env -> DefGroups -> Unique DefGroups
linearEffectOptimize' loaded penv defs
  = do let (_,_,r) = runQueryForDefs loaded return (loadedModule loaded) leo
       return $ fromMaybe defs r

runQueryForDefs loaded loadModuleFromSource mod query =
  let cid = ExprContextId (-1) (modName mod)
      modCtx = ModuleC cid mod (modName mod)
      result = runFix (createPrimitives >> query) (DEnv 3 BasicEnvs modCtx modCtx (EnvTail TopCtx) "" "" loadModuleFromSource ()) (State loaded M.empty 0 M.empty 0 Nothing M.empty ())
  in case result of
    (a, b, s) -> (a, b, finalResult s)

findOperationApplications :: ExprContext -> FixDemandR () () () [ExprContext]
findOperationApplications ctx
  = do
    -- If it is already known that it is linear, then don't do anything 
    -- otherwise, initialize the demand analysis to determine callers of the function this application is enclosed within
    -- If the function is only called within a context where handlers are inserted which are linear, then specialize the enclosing function
      return []

--------------------------------------------------------------------------
-- Definition groups - at the top level we can change the types -- since we can copy and specialize definitions
--------------------------------------------------------------------------
leo :: FixDemand DefGroups () ()
leo
  = do
      ctx <- currentContext <$> getEnv
      results <- case ctx of
        ModuleC cid mod _ -> do
          visitChildrenCtxs (\dgs -> concat dgs) ctx (
                do
                  ctx <- currentContext <$> getEnv
                  case ctx of
                    DefCNonRec _ _ _ d -> return [d]
                    DefCRec _ _ _ _ ds -> return [ds]
                    _ -> error "leo: unexpected context"
              )
        _ -> error "leo: unexpected context"
      setResult results
      return $ BL N


