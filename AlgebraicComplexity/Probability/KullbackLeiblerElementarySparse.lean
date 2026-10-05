/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.KullbackLeiblerBasic
import AlgebraicComplexity.Probability.SupportRestrictionCore

/-!
# Structural-zero extension of the elementary quadratic KL bound

`KullbackLeiblerBasic.lean` proves a derivative-free, two-sided coordinatewise KL estimate against
a full-support reference.  This file transports it to sparse laws under absolute continuity.
-/

namespace AlgebraicComplexity
namespace ProbabilityVector

universe u

variable {I : Type u} [Fintype I]

/-- Structural-zero form of the derivative-free two-sided coordinatewise KL bound. -/
theorem quarter_sq_sub_weight_le_klDiv_of_absoluteContinuity_elementary
    (p q : ProbabilityVector I) (hac : p.IsAbsolutelyContinuous q) (i : I) :
    (p.weight i - q.weight i) ^ 2 / 4 ≤ p.klDiv q := by
  by_cases hqi : 0 < q.weight i
  · let j : q.PositiveSupport := ⟨i, hqi⟩
    have h := quarter_sq_sub_weight_le_klDiv_elementary
      (restrictToPositiveSupport p q hac) q.positiveSupportRestriction
      q.positiveSupportRestriction_pos j
    simpa only [j, restrictToPositiveSupport_weight,
      positiveSupportRestriction_weight,
      restrictToPositiveSupport_klDiv p q hac] using h
  · have hqzero : q.weight i = 0 :=
      weight_eq_zero_of_not_mem_positiveSupport q i hqi
    have hpzero : p.weight i = 0 := hac i hqzero
    have hnonneg := klDiv_nonneg
      (restrictToPositiveSupport p q hac) q.positiveSupportRestriction
        q.positiveSupportRestriction_pos
    rw [restrictToPositiveSupport_klDiv p q hac] at hnonneg
    simpa [hpzero, hqzero] using hnonneg

end ProbabilityVector
end AlgebraicComplexity
