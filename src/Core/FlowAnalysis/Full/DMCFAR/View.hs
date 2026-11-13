-----------------------------------------------------------------------------
-- A readable report of the results of the full HMCFA analysis (DMCFAR, with rebinding):
-- what every expression evaluates to and what every variable is bound to,
-- at each timestamp, shown in terms of the source program.
-- The code is shared with the other variant, in ../HMCFAView.inc.
-- See analysis/hmcfa-viewer.md for the roadmap.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings, CPP #-}
module Core.FlowAnalysis.Full.DMCFAR.View( hmcfaReport, hmcfaJson ) where

import Core.FlowAnalysis.Full.DMCFAR.DMCFA
import Core.FlowAnalysis.Full.DMCFAR.AbstractValue
import Core.FlowAnalysis.Full.DMCFAR.Monad
import Core.FlowAnalysis.Full.DMCFAR.Syntax ()   -- Label instances for the fixpoint cache

#include "../HMCFAView.inc"

-- | The expression and timestamp of a step that produces an expression's value (here the timestamp is part of the environment).
evalStep :: Conf -> Maybe (ExprContext, CombinedCtx)
evalStep (CEval ctx (time, _)) = Just (ctx, time)
-- An application whose last argument performed an operation is finished when the resumed continuation
-- continues its frame: that step has the application's value (at the timestamp it continues in).
evalStep (CContinue (RVAddr _) (FApp _ [] _ eApp _) time) = Just (eApp, time)
evalStep _                     = Nothing
