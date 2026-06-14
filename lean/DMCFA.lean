/-
  DMCFA: Formalization of Concrete Big-Step Equivalence for Effect Handlers

  This formalization proves that our big-step semantics with environments and stores
  is equivalent to the substitution-based semantics of Bauer & Pretnar.
-/

import DMCFA.Syntax
import DMCFA.Components
import DMCFA.Semantics
import DMCFA.Lemmas
import DMCFA.TimestampedCompleteness
import DMCFA.TimestampedSoundness
import DMCFA.Abstraction
import DMCFA.LNBPSemantics
import DMCFA.LNBPSyntax
import DMCFA.LNCompleteness
import DMCFA.LNComponents
import DMCFA.LNEquivalence
import DMCFA.LNLemmas
import DMCFA.LNSemantics
import DMCFA.LNSoundness
import DMCFA.LNSyntax
import DMCFA.LNBridge
