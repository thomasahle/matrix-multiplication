/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.PooledMarginalProfileCore
import AlgebraicComplexity.Probability.IntegralProfileCore
import AlgebraicComplexity.Probability.KullbackLeiblerElementarySparse
import AlgebraicComplexity.Probability.PooledMarginalProjection

/-!
# Entropy loss from a pooled-parent profile deviation

This module is the analytic half of pooled-marginal type concentration.  It turns an exact
integral pooled profile into a feasible probability law and applies the information-projection
inequality.  The finite type enumeration and multinomial estimate live separately in
`PooledMarginalTypeConcentration.lean`.
-/

namespace AlgebraicComplexity
namespace WordType

universe u₁ u₂ u₃ u₄

variable {S : Type u₁} {U : Type u₂} {A : Type u₃} {P : Type u₄}
variable [Fintype S] [Fintype U] [Fintype A] [Fintype P]
variable [DecidableEq U] [DecidableEq A] [DecidableEq P]

/-- Coordinatewise deviation of the empirical parent profile from the reference parent law. -/
def PooledParentProfileHasDeviation
    (M : SparsePooledMarginalProjectionModel S U A)
    (parent : S → P) (profile : S → ℕ) (epsilon : ℝ) : Prop :=
  ∃ p,
    epsilon ≤ abs (
      (mappedType parent profile p : ℝ) / (profileMass profile : ℝ) -
        (M.reference.pushforward parent).weight p)

/-- A parent-coordinate deviation lowers conditional profile entropy by a fixed quadratic
amount.  The reference conditional entropy may be irrational; the correction is elementary and
uniform over all positive-mass empirical profiles. -/
theorem profileConditionalEntropy_le_reference_sub_quarter_sq_of_parentDeviation
    (M : SparsePooledMarginalProjectionModel S U A)
    (parent : S → P)
    (profile : S → ℕ) (hmass : 0 < profileMass profile)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hprofile : IsPooledMarginalProfile M profile)
    (hdeviation : PooledParentProfileHasDeviation M parent profile epsilon) :
    profileEntropyNats profile -
        profileEntropyNats (mappedType M.coarse profile) ≤
      M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4 := by
  let q := normalizedProfileProbability profile hmass
  have hq : M.IsFeasible q :=
    normalizedProfileProbability_isPooledFeasible M profile hmass hprofile
  have hprojection := M.conditionalEntropy_add_parentKl_le parent q hq
  obtain ⟨p, hp⟩ := hdeviation
  have hp' : epsilon ≤ abs (
      (q.pushforward parent).weight p -
        (M.reference.pushforward parent).weight p) := by
    simpa only [q, normalizedProfileProbability_pushforward_weight] using hp
  have hsquare : epsilon ^ 2 ≤
      ((q.pushforward parent).weight p -
        (M.reference.pushforward parent).weight p) ^ 2 := by
    have hsquareAbs := (sq_le_sq₀ hepsilon (abs_nonneg _)).2 hp'
    simpa only [sq_abs] using hsquareAbs
  have hcoordinate :=
    ProbabilityVector.quarter_sq_sub_weight_le_klDiv_of_absoluteContinuity_elementary
      (q.pushforward parent) (M.reference.pushforward parent)
      (hq.1.pushforward parent) p
  have hgap : epsilon ^ 2 / 4 ≤
      (q.pushforward parent).klDiv (M.reference.pushforward parent) := by
    linarith
  have hcoarsePush :
      q.pushforward M.coarse =
        normalizedProfileProbability (mappedType M.coarse profile) (by
          simpa only [profileMass_mappedType] using hmass) := by
    apply ProbabilityVector.ext
    funext u
    rw [normalizedProfileProbability_pushforward_weight,
      normalizedProfileProbability_weight, profileMass_mappedType]
  change q.entropy - (q.pushforward M.coarse).entropy +
      (q.pushforward parent).klDiv (M.reference.pushforward parent) ≤
        M.reference.conditionalEntropy M.coarse at hprojection
  rw [show q.entropy = profileEntropyNats profile by
      exact normalizedProfileProbability_entropy profile hmass,
    hcoarsePush,
    normalizedProfileProbability_entropy] at hprojection
  linarith

end WordType
end AlgebraicComplexity
