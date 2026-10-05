/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Certified logarithm enclosures

Reusable rational lower and upper bounds for logarithms, based on the atanh series

`log ((1+x)/(1-x)) = 2 * ∑ k, x^(2k+1)/(2k+1)`.

The remainder bound is deliberately simple, making closed rational certificates easy for
`norm_num` to verify.
-/

namespace AlgebraicComplexity.Analysis

open scoped BigOperators

noncomputable section

/-- The first `n` terms of the atanh half-log series. -/
def atanhPartial (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, x ^ (2 * k + 1) / (2 * k + 1)

/-- A geometric upper bound for the remaining half-log series. -/
def atanhRemainder (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n + 1) / (1 - x ^ 2)

/-- A nonempty atanh partial sum is positive at a positive argument.

Proof sketch: every summand is nonnegative, while the summand at index zero is exactly `x` and
therefore positive. This structural proof avoids normalizing a large closed rational sum merely to
establish its sign. -/
theorem atanhPartial_pos {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 0 < n) :
    0 < atanhPartial x n := by
  unfold atanhPartial
  apply Finset.sum_pos'
  · intro k _
    exact div_nonneg (pow_nonneg hx.le _) (by positivity)
  · refine ⟨0, by simpa using hn, ?_⟩
    simpa using hx

theorem atanhPartial_le_halfLogRatio {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ) :
    atanhPartial x n ≤ (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) := by
  simpa [atanhPartial] using Real.sum_range_le_log_div hx₀ hx₁ n

theorem halfLogRatio_le_atanhPartial_add_remainder
    {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ) :
    (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x)) ≤
      atanhPartial x n + atanhRemainder x n := by
  simpa [atanhPartial, atanhRemainder] using Real.log_div_le_sum_range_add hx₀ hx₁ n

/-- A lower enclosure for a full logarithm ratio. -/
def logRatioLower (x : ℝ) (n : ℕ) : ℝ :=
  2 * atanhPartial x n

/-- An upper enclosure for a full logarithm ratio. -/
def logRatioUpper (x : ℝ) (n : ℕ) : ℝ :=
  2 * (atanhPartial x n + atanhRemainder x n)

theorem logRatioLower_le {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ) :
    logRatioLower x n ≤ Real.log ((1 + x) / (1 - x)) := by
  have h := atanhPartial_le_halfLogRatio hx₀ hx₁ n
  dsimp [logRatioLower]
  linarith

theorem le_logRatioUpper {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (n : ℕ) :
    Real.log ((1 + x) / (1 - x)) ≤ logRatioUpper x n := by
  have h := halfLogRatio_le_atanhPartial_add_remainder hx₀ hx₁ n
  dsimp [logRatioUpper]
  linarith

end

end AlgebraicComplexity.Analysis
