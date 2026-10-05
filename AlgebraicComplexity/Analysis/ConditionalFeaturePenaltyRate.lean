/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalFeatureTypeCountingGrowth

/-!
# Bit-rate form of the conditional-feature penalty base

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*, divides a compatible ordered-parent count
by the type-class count of one fixed fine block.  The generic conditional-feature API records this
division in natural-logarithmic form as `conditionalFeatureEntropyPenaltyBase`.  Certificate
calculations instead record all entropy rates in bits.

This module proves the exact conversion between those two presentations.  If the joint count has
per-repetition exponent `m log(2) U`, then division by the fixed source type leaves exponent
`m log(2) (U - H₂(source))`, equivalently base `2 ^ (m (U - H₂(source)))`.

These identities formalize the final `Q / P` cancellation in [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:388-439`.  They introduce no compatibility family,
certificate data, asymptotic extraction, or matrix-multiplication endpoint.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.WordType

universe u v

variable {S : Type u} [Fintype S]

/-- Writing the joint exponent in bits exposes the exact source-entropy subtraction in the
conditional-feature penalty base.

Proof sketch: after unfolding integral-profile entropy in bits, both exponents differ only by
distributivity and division by the nonzero number `log 2`. -/
theorem conditionalFeatureEntropyPenaltyBase_eq_exp_entropyBits_sub
    (sourceProfile : S → ℕ) (jointEntropyBits : ℝ) :
    conditionalFeatureEntropyPenaltyBase sourceProfile
        ((profileMass sourceProfile : ℝ) * Real.log 2 * jointEntropyBits) =
      Real.exp ((profileMass sourceProfile : ℝ) * Real.log 2 *
        (jointEntropyBits - profileEntropyBits sourceProfile)) := by
  have hlogTwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold conditionalFeatureEntropyPenaltyBase profileEntropyBits
  congr 1
  field_simp

/-- Base-two form of
`conditionalFeatureEntropyPenaltyBase_eq_exp_entropyBits_sub`. -/
theorem conditionalFeatureEntropyPenaltyBase_eq_two_rpow_entropyBits_sub
    (sourceProfile : S → ℕ) (jointEntropyBits : ℝ) :
    conditionalFeatureEntropyPenaltyBase sourceProfile
        ((profileMass sourceProfile : ℝ) * Real.log 2 * jointEntropyBits) =
      (2 : ℝ) ^ ((profileMass sourceProfile : ℝ) *
        (jointEntropyBits - profileEntropyBits sourceProfile)) := by
  rw [conditionalFeatureEntropyPenaltyBase_eq_exp_entropyBits_sub
    sourceProfile jointEntropyBits,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

end AlgebraicComplexity.WordType
