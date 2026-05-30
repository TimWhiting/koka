/-
  DMCFA: Formalization of Concrete Big-Step Equivalence for Effect Handlers

  This formalization proves that our big-step semantics with environments and stores
  is equivalent to the substitution-based semantics of Bauer & Pretnar.
-/

import DMCFA.Syntax
import DMCFA.BPSyntax
import DMCFA.Components
import DMCFA.Semantics
import DMCFA.BPSemantics
import DMCFA.Equivalence
import DMCFA.Lemmas
import DMCFA.Completeness
import DMCFA.Soundness
import DMCFA.TimestampedCompleteness
import DMCFA.TimestampedSoundness
import DMCFA.Abstraction
