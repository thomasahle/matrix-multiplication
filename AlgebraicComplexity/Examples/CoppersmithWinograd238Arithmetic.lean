/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.LogConstants

/-!
# Exact arithmetic for the classical Coppersmith--Winograd `2.38` bound

This lightweight client contains only the directed real-arithmetic certificate used by the
`q = 6` CW-square proof.  Tensor constructions, type extraction, and the value formalism live in
separate modules.  Keeping the arithmetic here makes the numerical proof quick to elaborate and
easy to audit independently.

Every logarithm is bounded by a finite rational partial sum of the atanh series from
`Analysis/Log.lean`.  The proof uses no floating-point evaluation or numerical oracle.  The final
theorem compares `1971483 * log 64` with the logarithm of the assembled value lower bound.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity.Analysis

noncomputable section

/-- Add an exact power of two to a certified atanh lower bound.

If `y = 2^m (1+x)/(1-x)`, the atanh certificate for the ratio and the standard certified lower
bound for `log 2` give the displayed lower bound for `log y`. -/
private theorem le_log_of_powTwo_logRatioLower
    (m steps : ℕ) {x y c : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy : (2 : ℝ) ^ m * ((1 + x) / (1 - x)) = y)
    (hc : c ≤ (m : ℝ) * (693147 / 1000000 : ℝ) + logRatioLower x steps) :
    c ≤ Real.log y := by
  have hratioPos : 0 < (1 + x) / (1 - x) := by positivity
  calc
    c ≤ (m : ℝ) * (693147 / 1000000 : ℝ) + logRatioLower x steps := hc
    _ ≤ (m : ℝ) * Real.log 2 + Real.log ((1 + x) / (1 - x)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left log_two_ge (Nat.cast_nonneg m))
        (logRatioLower_le hx0 hx1 steps)
    _ = Real.log y := by
      rw [← Real.log_pow]
      rw [← Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hratioPos.ne']
      rw [hy]

/-! ## Directed logarithm certificates -/

/-- Certified lower bound for the first outer marginal ratio. -/
theorem cw238_log_outer0_ge :
    (2055541 : ℝ) / 1000000 ≤ Real.log (1971483 / 252396 : ℝ) := by
  apply le_log_of_powTwo_logRatioLower 2 6
      (x := (320633 / 993689 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the second outer marginal ratio. -/
theorem cw238_log_outer1_ge :
    (829890 : ℝ) / 1000000 ≤ Real.log (1971483 / 859758 : ℝ) := by
  apply le_log_of_powTwo_logRatioLower 1 6
      (x := (83989 / 1230333 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the third outer marginal ratio. -/
theorem cw238_log_outer2_ge :
    (890050 : ℝ) / 1000000 ≤ Real.log (1971483 / 809560 : ℝ) := by
  apply le_log_of_powTwo_logRatioLower 1 6
      (x := (352363 / 3590603 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the fourth outer marginal ratio. -/
theorem cw238_log_outer3_ge :
    (3688413 : ℝ) / 1000000 ≤ Real.log (1971483 / 49310 : ℝ) := by
  apply le_log_of_powTwo_logRatioLower 5 6
      (x := (393563 / 3549403 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the fifth outer marginal ratio. -/
theorem cw238_log_outer4_ge :
    (8365244 : ℝ) / 1000000 ≤ Real.log (1971483 / 459 : ℝ) := by
  apply le_log_of_powTwo_logRatioLower 12 6
      (x := (30473 / 1283849 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the inner factor `log 74`. -/
theorem cw238_log_seventyFour_ge :
    (4304064 : ℝ) / 1000000 ≤ Real.log 74 := by
  apply le_log_of_powTwo_logRatioLower 6 6 (x := (5 / 69 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the inner imbalance factor `log (37/36)`. -/
theorem cw238_log_thirtySeven_thirtySix_ge :
    (27398 : ℝ) / 1000000 ≤ Real.log (37 / 36 : ℝ) := by
  apply le_log_of_powTwo_logRatioLower 0 6 (x := (1 / 73 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the ordinary constituent factor `log 12`. -/
theorem cw238_log_twelve_ge :
    (2484906 : ℝ) / 1000000 ≤ Real.log 12 := by
  apply le_log_of_powTwo_logRatioLower 3 6 (x := (1 / 5 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the ordinary constituent factor `log 38`. -/
theorem cw238_log_thirtyEight_ge :
    (3637585 : ℝ) / 1000000 ≤ Real.log 38 := by
  apply le_log_of_powTwo_logRatioLower 5 6 (x := (3 / 35 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-- Certified lower bound for the exceptional constituent factor `log 6`. -/
theorem cw238_log_six_ge :
    (1791759 : ℝ) / 1000000 ≤ Real.log 6 := by
  apply le_log_of_powTwo_logRatioLower 2 6 (x := (1 / 5 : ℝ)) <;>
    norm_num [logRatioLower, atanhPartial, Finset.sum_range_succ]

/-! ## The final scalar separation -/

/-- The exact rational enclosures separate the logarithmic cost of rank `64` from the assembled
CW-square value lower bound.

Proof sketch: upper-bound the logarithm on the left by `log 2 ≤ 0.693148`; lower-bound every
positive term on the right by the ten certificates above and `log 2 ≥ 0.693147`.  After these
directed replacements, `norm_num` verifies a strict rational inequality.  Independently
collecting those displayed rational endpoints gives the exact unnormalized reserve
`129293274019 / 12500000 > 0`; this is only a human-audit checksum, while the proof below asks
Lean to establish the comparison directly. -/
theorem cw238_scalar_log_inequality :
    (1971483 : ℝ) * (6 * Real.log 2) <
      252396 * Real.log (1971483 / 252396 : ℝ) +
      859758 * Real.log (1971483 / 859758 : ℝ) +
      809560 * Real.log (1971483 / 809560 : ℝ) +
      49310 * Real.log (1971483 / 49310 : ℝ) +
      459 * Real.log (1971483 / 459 : ℝ) +
      810446 * Real.log 2 +
      10952 * Real.log 74 + 394272 * Real.log (37 / 36 : ℝ) +
      (119 / 150 : ℝ) *
        (147930 * Real.log 12 + 606504 * Real.log 38 + 2398488 * Real.log 6) := by
  calc
    (1971483 : ℝ) * (6 * Real.log 2) ≤
        1971483 * (6 * (693148 / 1000000 : ℝ)) := by
      nlinarith [log_two_le]
    _ <
        252396 * (2055541 / 1000000 : ℝ) +
        859758 * (829890 / 1000000 : ℝ) +
        809560 * (890050 / 1000000 : ℝ) +
        49310 * (3688413 / 1000000 : ℝ) +
        459 * (8365244 / 1000000 : ℝ) +
        810446 * (693147 / 1000000 : ℝ) +
        10952 * (4304064 / 1000000 : ℝ) +
        394272 * (27398 / 1000000 : ℝ) +
        (119 / 150 : ℝ) *
          (147930 * (2484906 / 1000000 : ℝ) +
            606504 * (3637585 / 1000000 : ℝ) +
            2398488 * (1791759 / 1000000 : ℝ)) := by
      norm_num
    _ ≤
        252396 * Real.log (1971483 / 252396 : ℝ) +
        859758 * Real.log (1971483 / 859758 : ℝ) +
        809560 * Real.log (1971483 / 809560 : ℝ) +
        49310 * Real.log (1971483 / 49310 : ℝ) +
        459 * Real.log (1971483 / 459 : ℝ) +
        810446 * Real.log 2 +
        10952 * Real.log 74 + 394272 * Real.log (37 / 36 : ℝ) +
        (119 / 150 : ℝ) *
          (147930 * Real.log 12 + 606504 * Real.log 38 + 2398488 * Real.log 6) := by
      nlinarith [log_two_ge, cw238_log_outer0_ge, cw238_log_outer1_ge,
        cw238_log_outer2_ge, cw238_log_outer3_ge, cw238_log_outer4_ge,
        cw238_log_seventyFour_ge, cw238_log_thirtySeven_thirtySix_ge,
        cw238_log_twelve_ge, cw238_log_thirtyEight_ge, cw238_log_six_ge]

end

end AlgebraicComplexity.Examples
