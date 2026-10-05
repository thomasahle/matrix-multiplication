/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.SupportRestrictionDataProcessing

/-!
# Axiom audit for sparse deterministic data processing

This focused audit checks every public declaration in the lightweight positive-support
pushforward and KL-data-processing leaf.
-/

set_option autoImplicit false

open AlgebraicComplexity

#assert_axioms ProbabilityVector.restrictToPositiveSupport_pushforward
#assert_axioms ProbabilityVector.positiveSupportRestriction_pushforward
#assert_axioms ProbabilityVector.IsAbsolutelyContinuous.pushforward
#assert_axioms ProbabilityVector.positiveSupportMap
#assert_axioms ProbabilityVector.positiveSupportMap_val
#assert_axioms ProbabilityVector.positiveSupportMap_surjective
#assert_axioms ProbabilityVector.restrictToPositiveSupport_pushforward_positiveSupportMap
#assert_axioms ProbabilityVector.positiveSupportRestriction_pushforward_positiveSupportMap
#assert_axioms ProbabilityVector.klDiv_pushforward_le_of_absoluteContinuity
#assert_axioms ProbabilityVector.klDivBits_pushforward_le_of_absoluteContinuity
