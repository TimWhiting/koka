-----------------------------------------------------------------------------
-- A readable report of the results of the full HMCFA analysis (DMCFA):
-- what every expression evaluates to and what every variable is bound to,
-- at each timestamp, shown in terms of the source program.
-- The code is shared with the other variant, in ../HMCFAView.inc.
-- See analysis/hmcfa-viewer.md for the roadmap.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings, CPP #-}
module Core.FlowAnalysis.Full.DMCFA.View( hmcfaReport, hmcfaJson ) where

import Core.FlowAnalysis.Full.DMCFA.DMCFA
import Core.FlowAnalysis.Full.DMCFA.AbstractValue
import Core.FlowAnalysis.Full.DMCFA.Monad
import Core.FlowAnalysis.Full.DMCFA.Syntax ()   -- Label instances for the fixpoint cache

#include "../HMCFAView.inc"

-- | The expression and timestamp of a step that produces an expression's value.
evalStep :: Conf -> Maybe (ExprContext, CombinedCtx)
evalStep (CEval ctx _ time) = Just (ctx, time)
-- An application whose last argument performed an operation is finished when the resumed continuation
-- continues its frame: that step has the application's value (at the timestamp it continues in).
evalStep (CContinue (RVAddr _) (FApp _ [] _ eApp _) time) = Just (eApp, time)
evalStep _                  = Nothing
