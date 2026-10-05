/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicIntegralProfileCompatibilityRows

set_option autoImplicit false

/-!
# Integral-profile semantics of dyadic compatibility rows

The division-free compatibility-row identity is proved in the preceding lightweight module.
This file derives its normalized Shannon forms.  Under the natural CW normalization, in which
the separately labelled left and right occurrence table has twice the parent mass, the evaluator
branch is

`-2 * logRate p_comp + H(parent) - 2 * H(split | visible)`.

Equivalently, this is
`-2 * logRate p_comp + 2 * I(visible; split) + H(parent) - 2 * H(split)`.
The parent-versus-occurrence term is essential: the recursive evaluator uses the entropy of the
concatenated parent complete-split law, not the entropy of one labelled child occurrence.  The
factor two remains at self-complementary states because left and right occurrences retain their
labels.

No tensor, certificate row, generated datum, or asymptotic estimate occurs here.
-/

open scoped BigOperators

namespace AlgebraicComplexity.CompatibleSplit

open AlgebraicComplexity
open AlgebraicComplexity.WordType
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicEntropyForm
open MatrixMultiplication.DyadicHomogeneousEntropy
open MatrixMultiplication.DyadicIntegralProfileEntropy
open MatrixMultiplication.HomogeneousEntropyDual
open MatrixMultiplication.SimplifiedExponentRootRecurrence

noncomputable section

universe u v w x

namespace SplitRequirements

variable {C : Type u} {L : Type v} {Z : Type w}
variable [Fintype C] [DecidableEq C]
variable [Fintype L] [DecidableEq L]
variable [Fintype Z] [DecidableEq Z]

/-- Normalized Shannon form of the compatibility branch under an explicit equal-mass hypothesis.

This theorem is useful for one-sided occurrence encodings.  The two-sided labelled CW occurrence
table does **not** satisfy its hypothesis: that table has twice the mass of its parent row. -/
theorem canonicalCompatibilityRows_rate_normalized_of_equal_mass
    {P : Type x} [Fintype P] [DecidableEq P]
    (S : SplitRequirements C L Z) (parentProfile : P → ℕ) (bits : ℕ)
    (hparentMass : profileMass parentProfile = profileMass S.usefulType)
    (hmass : 0 < profileMass S.usefulType) :
    ((S.canonicalCompatibilityRows parentProfile).rate bits) /
        mass bits (profileMass S.usefulType) =
      -S.compatibilityRateBits +
        profileEntropyNats parentProfile / Real.log 2 -
          rowEntropyMass S.typicalType /
            ((profileMass S.usefulType : ℝ) * Real.log 2) := by
  rw [S.canonicalCompatibilityRows_rate parentProfile bits,
    weightedEntropy_eq_mass_mul_profileEntropyBits, hparentMass]
  unfold compatibilityRateBits compatibilityRateLog mass
  have hprofileMass : (profileMass S.usefulType : ℝ) ≠ 0 := by
    exact_mod_cast hmass.ne'
  have hpow : (2 : ℝ) ^ bits ≠ 0 := by positivity
  have hlog : Real.log 2 ≠ 0 := by
    simpa using Real.log_ne_zero_of_pos_of_ne_one
      (by norm_num : (0 : ℝ) < 2) (by norm_num)
  field_simp [hprofileMass, hpow, hlog]
  <;> ring

/-- Normalized Shannon form for a two-sided labelled occurrence table.

This is the natural recursive CW scaling: every parent position contributes one labelled left and
one labelled right occurrence, including when the two underlying states are self-complementary.
Thus the useful, compatible, and typical occurrence tables have twice the parent mass, and every
occurrence-normalized conditional-entropy term enters the parent-normalized evaluator rate with
coefficient two. -/
theorem canonicalCompatibilityRows_rate_normalized_of_double_occurrence_mass
    {P : Type x} [Fintype P] [DecidableEq P]
    (S : SplitRequirements C L Z) (parentProfile : P → ℕ) (bits : ℕ)
    (hmassRatio : profileMass S.usefulType = 2 * profileMass parentProfile)
    (hparentMass : 0 < profileMass parentProfile) :
    ((S.canonicalCompatibilityRows parentProfile).rate bits) /
        mass bits (profileMass parentProfile) =
      -(2 : ℝ) * S.compatibilityRateBits +
        profileEntropyNats parentProfile / Real.log 2 -
          2 * (rowEntropyMass S.typicalType /
            ((profileMass S.usefulType : ℝ) * Real.log 2)) := by
  rw [S.canonicalCompatibilityRows_rate parentProfile bits,
    weightedEntropy_eq_mass_mul_profileEntropyBits]
  unfold compatibilityRateBits compatibilityRateLog mass
  rw [hmassRatio]
  have hprofileMass : (profileMass parentProfile : ℝ) ≠ 0 := by
    exact_mod_cast hparentMass.ne'
  have hpow : (2 : ℝ) ^ bits ≠ 0 := by positivity
  have hlog : Real.log 2 ≠ 0 := by
    simpa using Real.log_ne_zero_of_pos_of_ne_one
      (by norm_num : (0 : ℝ) < 2) (by norm_num)
  push_cast
  field_simp [hprofileMass, hpow, hlog]
  <;> ring

end SplitRequirements

end

end AlgebraicComplexity.CompatibleSplit
