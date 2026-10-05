/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.FiniteJointDisintegrationNormalized
import MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualCore

set_option autoImplicit false

/-!
# Normalized-profile support for restricted conditional integer duals

Structural zeroes in a nonzero integral joint profile force its zero-safe conditional rows to
live on the corresponding legal fibers. This adapter contains no profile-entropy inequality.

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

namespace MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDual

open AlgebraicComplexity

noncomputable section

universe u v

/-- A normalized integral joint profile inherits legal-row support from structural zeroes in the
profile, at every positive-mass parent row. -/
theorem normalizedJointProfileRows_supportedOnPositiveParent
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (profile : Z × U → ℕ) (hmass : 0 < WordType.profileMass profile)
    (legal : Z → U → Prop)
    (hprofile : ∀ z u, ¬legal z u → profile (z, u) = 0) :
    RowsSupportedOnPositiveParent
      (WordType.normalizedJointProfileParent profile hmass)
      (WordType.normalizedJointProfileRows profile hmass) legal := by
  intro z hz u hu
  unfold WordType.normalizedJointProfileRows
  rw [ProbabilityVector.conditionalSnd_weight_of_ne]
  · simp [WordType.normalizedProfileProbability_weight, hprofile z u hu]
  · exact hz.ne'

/-- Positive normalized parent mass forces the corresponding legal fiber to be nonempty when the
integral profile is structurally zero off that fiber. -/
theorem exists_legal_of_normalizedJointProfileParent_weight_pos
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (profile : Z × U → ℕ) (hmass : 0 < WordType.profileMass profile)
    (legal : Z → U → Prop)
    (hprofile : ∀ z u, ¬legal z u → profile (z, u) = 0)
    (z : Z)
    (hz : 0 < (WordType.normalizedJointProfileParent profile hmass).weight z) :
    ∃ u, legal z u := by
  classical
  by_contra hnone
  have hillegal : ∀ u, ¬legal z u := by
    intro u hu
    exact hnone ⟨u, hu⟩
  have hparentzero :
      (WordType.normalizedJointProfileParent profile hmass).weight z = 0 := by
    unfold WordType.normalizedJointProfileParent
    rw [← ProbabilityVector.sum_snd_weight_eq_pushforward_fst_weight]
    apply Finset.sum_eq_zero
    intro u _
    simp [WordType.normalizedProfileProbability_weight,
      hprofile z u (hillegal u)]
  exact hz.ne' hparentzero

end

end MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDual
