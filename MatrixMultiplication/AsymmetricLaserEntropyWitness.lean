/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserData
import AlgebraicComplexity.Probability.EntropyDefs
import Mathlib.Tactic.Ring

/-!
# Zero-aware entropy witnesses for arbitrary-denominator finite laws

This is the normalization and sign accounting in the directed reconstruction of
`better_bound/paper.tex:2505-2512`, for the finite probability laws appearing in
[duan2023faster], `global_value.tex:286-309,332-378`.

For a normalized count list `n` of total `D > 0`, the existing Shannon entropy is
`log₂ D - sum_i (n_i / D) * log₂ n_i`. Lower entropy bounds use a lower denominator
logarithm and upper numerator logarithms; upper bounds reverse these choices. The denominator
is arbitrary, not silently replaced by a power of two. A zero-count letter stays in the law,
but needs no logarithm enclosure. Native support completeness is checked by the caller's
profile decoder, independently of this purely arithmetic theorem.

Proof sketch: expand the logarithm of each positive rational weight, use the zero convention
at zero weights, and factor out the normalized sum. Monotonicity of the remaining finite
nonnegative weighted sum then gives both directed endpoints.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.AsymmetricLaserData

/-- Entropy of a normalized finite count list as a log-linear form, including zero entries. -/
theorem FiniteLaw.entropyBits_eq_log_denominator_sub (law : FiniteLaw) (h : law.Valid) :
    (law.toRational.toReal (law.toRational_isProbability h)).entropyBits =
      Real.log (law.denominator : ℝ) / Real.log 2 -
        ∑ i, ((law.profile i : ℝ) / (law.denominator : ℝ)) *
          (Real.log (law.profile i : ℝ) / Real.log 2) := by
  have hden : (law.denominator : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt h.1)
  have hweight (i : Fin law.counts.length) :
      (law.toRational.toReal (law.toRational_isProbability h)).weight i =
        (law.profile i : ℝ) / (law.denominator : ℝ) := by
    simp only [RationalProbabilityData.toReal_weight, FiniteLaw.toRational,
      Rat.cast_div, Rat.cast_natCast]
  have hsum : (∑ i, (law.profile i : ℝ) / (law.denominator : ℝ)) = 1 := by
    simpa only [hweight] using
      (law.toRational.toReal (law.toRational_isProbability h)).total
  unfold ProbabilityVector.entropyBits ProbabilityVector.entropy
  rw [Finset.sum_div]
  calc
    ∑ i, Real.negMulLog
        ((law.toRational.toReal (law.toRational_isProbability h)).weight i) / Real.log 2 =
      ∑ i, (((law.profile i : ℝ) / (law.denominator : ℝ)) *
          (Real.log (law.denominator : ℝ) / Real.log 2) -
        ((law.profile i : ℝ) / (law.denominator : ℝ)) *
          (Real.log (law.profile i : ℝ) / Real.log 2)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hweight]
      by_cases hi : law.profile i = 0
      · simp [hi, Real.negMulLog]
      · rw [Real.negMulLog, Real.log_div (Nat.cast_ne_zero.mpr hi) hden]
        ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]

/-- Rational lower entropy endpoint; zero coefficients suppress unused numerator bounds. -/
def FiniteLaw.entropyLower (law : FiniteLaw) (denominatorLower : ℚ)
    (numeratorUpper : Fin law.counts.length → ℚ) : ℚ :=
  denominatorLower - ∑ i, law.toRational.weight i * numeratorUpper i

/-- Rational upper entropy endpoint, with the logarithm directions reversed. -/
def FiniteLaw.entropyUpper (law : FiniteLaw) (denominatorUpper : ℚ)
    (numeratorLower : Fin law.counts.length → ℚ) : ℚ :=
  denominatorUpper - ∑ i, law.toRational.weight i * numeratorLower i

/-- Lower logarithm of the denominator and upper positive-numerator logarithms bound entropy
from below. No logarithm premise is required at a legal zero-count letter. -/
theorem FiniteLaw.entropyLower_le (law : FiniteLaw) (h : law.Valid)
    (denominatorLower : ℚ) (numeratorUpper : Fin law.counts.length → ℚ)
    (hden : (denominatorLower : ℝ) ≤ Real.log (law.denominator : ℝ) / Real.log 2)
    (hnum : ∀ i, 0 < law.profile i →
      Real.log (law.profile i : ℝ) / Real.log 2 ≤ (numeratorUpper i : ℝ)) :
    (law.entropyLower denominatorLower numeratorUpper : ℝ) ≤
      (law.toRational.toReal (law.toRational_isProbability h)).entropyBits := by
  rw [law.entropyBits_eq_log_denominator_sub h]
  simp only [FiniteLaw.entropyLower, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul,
    FiniteLaw.toRational, Rat.cast_div, Rat.cast_natCast]
  apply sub_le_sub hden
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : law.profile i = 0
  · simp [hi]
  · exact mul_le_mul_of_nonneg_left (hnum i (Nat.pos_of_ne_zero hi))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Upper logarithm of the denominator and lower positive-numerator logarithms bound entropy
from above, still without removing zero-count symbols from the finite law. -/
theorem FiniteLaw.le_entropyUpper (law : FiniteLaw) (h : law.Valid)
    (denominatorUpper : ℚ) (numeratorLower : Fin law.counts.length → ℚ)
    (hden : Real.log (law.denominator : ℝ) / Real.log 2 ≤ (denominatorUpper : ℝ))
    (hnum : ∀ i, 0 < law.profile i →
      (numeratorLower i : ℝ) ≤ Real.log (law.profile i : ℝ) / Real.log 2) :
    (law.toRational.toReal (law.toRational_isProbability h)).entropyBits ≤
      (law.entropyUpper denominatorUpper numeratorLower : ℝ) := by
  rw [law.entropyBits_eq_log_denominator_sub h]
  simp only [FiniteLaw.entropyUpper, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul,
    FiniteLaw.toRational, Rat.cast_div, Rat.cast_natCast]
  apply sub_le_sub hden
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : law.profile i = 0
  · simp [hi]
  · exact mul_le_mul_of_nonneg_left (hnum i (Nat.pos_of_ne_zero hi))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end AlgebraicComplexity.AsymmetricLaserData
