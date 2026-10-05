/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralProfileCounts
import AlgebraicComplexity.Combinatorics.MappedType
import AlgebraicComplexity.Probability.PooledMarginalProjectionCore

/-!
# Integral profiles with pooled occurrence marginals: definitions

This definitions-only module records the denominator-form feasibility predicate used by
pooled-parent concentration.  It deliberately does not import normalization, entropy, KL
divergence, or multinomial estimates, so exact recursive-profile clients can use the semantic
interface without loading the analytic proof closure.
-/

namespace AlgebraicComplexity
namespace WordType

universe u₁ u₂ u₃

variable {S : Type u₁} {U : Type u₂} {A : Type u₃}
variable [Fintype S] [Fintype U] [Fintype A]
variable [DecidableEq U] [DecidableEq A]

/-- Integral form of feasibility for a sparse pooled-marginal projection.  Dividing the counts
by their total mass gives exactly `SparsePooledMarginalProjectionModel.IsFeasible`. -/
def IsPooledMarginalProfile
    (M : SparsePooledMarginalProjectionModel S U A)
    (profile : S → ℕ) : Prop :=
  (∀ s, M.reference.weight s = 0 → profile s = 0) ∧
    (∀ u,
      (mappedType M.coarse profile u : ℝ) / (profileMass profile : ℝ) =
        (M.reference.pushforward M.coarse).weight u) ∧
    ∀ a,
      (mappedType M.leftFeature profile a : ℝ) /
          (profileMass profile : ℝ) +
        (mappedType M.rightFeature profile a : ℝ) /
          (profileMass profile : ℝ) =
      (M.reference.pushforward M.leftFeature).weight a +
        (M.reference.pushforward M.rightFeature).weight a

end WordType
end AlgebraicComplexity
