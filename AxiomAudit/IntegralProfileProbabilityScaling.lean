/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.IntegralProfileProbabilityScaling

/-! Axiom audit for pointwise integral-profile scaling. -/

open AlgebraicComplexity

#assert_axioms WordType.normalizedProfileProbability_proportionalCounts_weight
