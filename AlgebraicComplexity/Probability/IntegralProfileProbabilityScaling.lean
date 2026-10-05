/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.IntegralProfileProbabilityCore

set_option autoImplicit false

/-!
# Pointwise scaling laws for normalized integral profiles

Positive proportional scaling leaves a normalized integral-profile probability vector unchanged.
This file records the pointwise form, which avoids carrying a dependent equality of complete
probability structures into concrete counting clients.
-/

namespace AlgebraicComplexity.WordType

universe u

variable {I : Type u} [Fintype I]

/-- Pointwise invariance of an empirical probability law under positive proportional scaling. -/
theorem normalizedProfileProbability_proportionalCounts_weight
    (profile : I → ℕ) (hmass : 0 < profileMass profile)
    (k : ℕ) (hk : 0 < k) (i : I) :
    (normalizedProfileProbability (proportionalCounts profile k) (by
      simpa [profileMass, proportionalCounts, Finset.sum_mul] using
        Nat.mul_pos hmass hk)).weight i =
      (profile i : ℝ) / profileMass profile := by
  simp only [normalizedProfileProbability_weight, proportionalCounts]
  have hscaledMass :
      profileMass (fun j ↦ profile j * k) = profileMass profile * k := by
    simp [profileMass, Finset.sum_mul]
  change ((profile i * k : ℕ) : ℝ) /
      (profileMass (fun j ↦ profile j * k) : ℝ) =
    (profile i : ℝ) / (profileMass profile : ℝ)
  rw [hscaledMass, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast hk.ne')

end AlgebraicComplexity.WordType
