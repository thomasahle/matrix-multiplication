/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.PooledMarginalProfileDefs
import AlgebraicComplexity.Probability.IntegralProfileProbabilityCore

/-!
# Integral profiles with pooled occurrence marginals

This lightweight module states the exact integral feasibility predicate used by pooled-parent
concentration and proves that normalization turns it into probability-vector feasibility.  It
contains no entropy inequality or multinomial estimate, so finite semantic clients can use the
profile interface without importing the analytic tail-bound closure.
-/

namespace AlgebraicComplexity
namespace WordType

universe u₁ u₂ u₃

variable {S : Type u₁} {U : Type u₂} {A : Type u₃}
variable [Fintype S] [Fintype U] [Fintype A]
variable [DecidableEq U] [DecidableEq A]

/-- Normalizing a positive-mass integral pooled profile produces a feasible probability law. -/
theorem normalizedProfileProbability_isPooledFeasible
    (M : SparsePooledMarginalProjectionModel S U A)
    (profile : S → ℕ) (hmass : 0 < profileMass profile)
    (hprofile : IsPooledMarginalProfile M profile) :
    M.IsFeasible (normalizedProfileProbability profile hmass) := by
  rcases hprofile with ⟨hsupport, hcoarse, hpool⟩
  constructor
  · intro s hs
    simp [normalizedProfileProbability_weight, hsupport s hs]
  constructor
  · apply ProbabilityVector.ext
    funext u
    rw [normalizedProfileProbability_pushforward_weight]
    exact hcoarse u
  · intro a
    rw [normalizedProfileProbability_pushforward_weight,
      normalizedProfileProbability_pushforward_weight]
    exact hpool a

end WordType
end AlgebraicComplexity
