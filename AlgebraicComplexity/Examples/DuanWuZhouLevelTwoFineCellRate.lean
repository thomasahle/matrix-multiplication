/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFinePairSum
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoConstituentValues
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellUniform

set_option autoImplicit false

/-!
# The `(0,2,2)` entropy rate is exactly the published value

Layer 4 (`AlgebraicComplexity/Examples/`).  `dwz63_exists_zeroFineCellWeight`
(`Examples/DuanWuZhouLevelTwoFineCellGeneral.lean`) delivers the weight

`(lowerBase ^ j * q ^ (Σ_p a_j(p) · middles p)) ^ tau`

for any `lowerBase` strictly below `2 ^ (mass · H(a))`.  This module identifies the limiting value
of that expression with `dwz63Val022 ^ mass`, over the committed atoms of `dwz63LogVal022`.

## The `tau` belongs on the outside

Worth stating explicitly, because it is easy to drop.  The natural-looking identity

`2 ^ (mass · H(a)) * q ^ (Σ_p a p · middles p) = dwz63Val022 ^ mass`   -- FALSE

is off by exactly the factor `tau` in the exponent: its left side is a *count* (the merged
matrix-multiplication dimension `N` of the fibre) while its right side is a *value*, and
`lem:non-rot-values` reads `V = N ^ tau`.  The true identity is

`(2 ^ (mass · H(a)) * q ^ (Σ_p a p · middles p)) ^ tau = dwz63Val022 ^ mass`,

whose logarithm is `dwz63_tau_mul_rate_eq_alphaTilde_two` below --- and that is exactly the shape
`dwz63_exists_zeroFineCellWeight` already produces, `tau` outermost.

## Exactness

Both sides are integer linear combinations of the same three atoms `log 2`, `log 3`,
`log (10^8/3477403)`, `log (5·10^7/46522597)` --- the last two being `log (1/a)` and
`log (1/(1-2a))` for `a = dwz63A` --- so `ring` closes the identity with no numeric slack at all.
No digits are re-derived: `dwz63LogVal022` is reused verbatim, and `log 6` is expanded to
`log 2 + log 3` exactly as the committed `dwz63LogVal112_eq_dwz112LogValue` does.

`dwz63AlphaTilde_two_eq_nine` is committed, so the `(2,0,2)` row is the same statement.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `lem:non-rot-values` (c).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

/-! ## The two nine-term readings -/

/-- The entropy of a fine-letter profile, as the nine-term table. -/
theorem dwz63_profileEntropyNats_eq {a : PositiveWord CWBlock 1 → ℕ} {m : ℕ}
    (hm : WordType.profileMass a = m) :
    WordType.profileEntropyNats a =
      Real.negMulLog ((a (.zero, .zero) : ℝ) / (m : ℝ))
        + Real.negMulLog ((a (.zero, .middle) : ℝ) / (m : ℝ))
        + Real.negMulLog ((a (.zero, .last) : ℝ) / (m : ℝ))
        + (Real.negMulLog ((a (.middle, .zero) : ℝ) / (m : ℝ))
          + Real.negMulLog ((a (.middle, .middle) : ℝ) / (m : ℝ))
          + Real.negMulLog ((a (.middle, .last) : ℝ) / (m : ℝ)))
        + (Real.negMulLog ((a (.last, .zero) : ℝ) / (m : ℝ))
          + Real.negMulLog ((a (.last, .middle) : ℝ) / (m : ℝ))
          + Real.negMulLog ((a (.last, .last) : ℝ) / (m : ℝ))) := by
  rw [WordType.profileEntropyNats, hm]
  exact dwz63_sum_finePair_expand (M := ℝ)
    (fun p ↦ Real.negMulLog ((a p : ℝ) / (m : ℝ)))

/-- The one-slice exponent of a fine-letter profile, as the nine-term table. -/
theorem dwz63_middleCountSum_eq (a : PositiveWord CWBlock 1 → ℕ) :
    (∑ p : PositiveWord CWBlock 1, a p * cwWordMiddleCount 1 p) =
      a (.zero, .zero) * cwWordMiddleCount 1 (.zero, .zero)
        + a (.zero, .middle) * cwWordMiddleCount 1 (.zero, .middle)
        + a (.zero, .last) * cwWordMiddleCount 1 (.zero, .last)
        + (a (.middle, .zero) * cwWordMiddleCount 1 (.middle, .zero)
          + a (.middle, .middle) * cwWordMiddleCount 1 (.middle, .middle)
          + a (.middle, .last) * cwWordMiddleCount 1 (.middle, .last))
        + (a (.last, .zero) * cwWordMiddleCount 1 (.last, .zero)
          + a (.last, .middle) * cwWordMiddleCount 1 (.last, .middle)
          + a (.last, .last) * cwWordMiddleCount 1 (.last, .last)) :=
  dwz63_sum_finePair_expand (M := ℕ) (fun p ↦ a p * cwWordMiddleCount 1 p)

/-! ## The nine entries of the `(0,2,2)` split row, and their middle counts -/

theorem dwz63_alphaTildeTwo_00 : dwz63AlphaTilde 2 (.zero, .zero) = 0 := rfl
theorem dwz63_alphaTildeTwo_0m : dwz63AlphaTilde 2 (.zero, .middle) = 0 := rfl
theorem dwz63_alphaTildeTwo_0l : dwz63AlphaTilde 2 (.zero, .last) = 6954806 := rfl
theorem dwz63_alphaTildeTwo_m0 : dwz63AlphaTilde 2 (.middle, .zero) = 0 := rfl
theorem dwz63_alphaTildeTwo_mm : dwz63AlphaTilde 2 (.middle, .middle) = 186090388 := rfl
theorem dwz63_alphaTildeTwo_ml : dwz63AlphaTilde 2 (.middle, .last) = 0 := rfl
theorem dwz63_alphaTildeTwo_l0 : dwz63AlphaTilde 2 (.last, .zero) = 6954806 := rfl
theorem dwz63_alphaTildeTwo_lm : dwz63AlphaTilde 2 (.last, .middle) = 0 := rfl
theorem dwz63_alphaTildeTwo_ll : dwz63AlphaTilde 2 (.last, .last) = 0 := rfl

/-- The three middle counts that carry a nonzero coefficient in the `(0,2,2)` row. -/
theorem dwz63_middleCountTwo_0l :
    cwWordMiddleCount 1 ((.zero, .last) : PositiveWord CWBlock 1) = 0 := by decide

theorem dwz63_middleCountTwo_mm :
    cwWordMiddleCount 1 ((.middle, .middle) : PositiveWord CWBlock 1) = 2 := by decide

theorem dwz63_middleCountTwo_l0 :
    cwWordMiddleCount 1 ((.last, .zero) : PositiveWord CWBlock 1) = 0 := by decide

/-! ## The `(0,2,2)` row, evaluated -/

/-- **The one-slice exponent of the `(0,2,2)` split row.**  Only the `(middle, middle)` letter has
middles, two of them, so the exponent is `2 * 186090388 = 2 * 2 * (1 - 2a) * 10 ^ 8`. -/
theorem dwz63_middleCountSum_alphaTilde_two :
    (∑ p : PositiveWord CWBlock 1, dwz63AlphaTilde 2 p * cwWordMiddleCount 1 p) = 372180776 := by
  rw [dwz63_middleCountSum_eq, dwz63_alphaTildeTwo_00, dwz63_alphaTildeTwo_0m,
    dwz63_alphaTildeTwo_0l, dwz63_alphaTildeTwo_m0, dwz63_alphaTildeTwo_mm,
    dwz63_alphaTildeTwo_ml, dwz63_alphaTildeTwo_l0, dwz63_alphaTildeTwo_lm,
    dwz63_alphaTildeTwo_ll]
  rw [dwz63_middleCountTwo_0l, dwz63_middleCountTwo_mm, dwz63_middleCountTwo_l0]
  norm_num

/-- **The entropy of the `(0,2,2)` split row**, over the two committed atoms `log (1/a)` and
`log (1/(1-2a))`. -/
theorem dwz63_profileEntropyNats_alphaTilde_two :
    WordType.profileEntropyNats (dwz63AlphaTilde 2) =
      2 * (3477403 / 100000000 : ℝ) * Real.log (100000000 / 3477403 : ℝ)
        + (46522597 / 50000000 : ℝ) * Real.log (50000000 / 46522597 : ℝ) := by
  have hneg : ∀ x : ℝ, Real.negMulLog x = x * Real.log x⁻¹ := by
    intro x
    rw [Real.negMulLog_eq_neg, Real.log_inv]
    ring
  rw [dwz63_profileEntropyNats_eq (dwz63_profileMass_alphaTilde 2), dwz63_alphaTildeTwo_00,
    dwz63_alphaTildeTwo_0m, dwz63_alphaTildeTwo_0l, dwz63_alphaTildeTwo_m0,
    dwz63_alphaTildeTwo_mm, dwz63_alphaTildeTwo_ml, dwz63_alphaTildeTwo_l0,
    dwz63_alphaTildeTwo_lm, dwz63_alphaTildeTwo_ll]
  rw [show ((0 : ℕ) : ℝ) / ((200000000 : ℕ) : ℝ) = 0 by norm_num, Real.negMulLog_zero,
    show ((6954806 : ℕ) : ℝ) / ((200000000 : ℕ) : ℝ) = 3477403 / 100000000 by norm_num,
    show ((186090388 : ℕ) : ℝ) / ((200000000 : ℕ) : ℝ) = 46522597 / 50000000 by norm_num]
  simp only [hneg]
  rw [show ((3477403 / 100000000 : ℝ))⁻¹ = 100000000 / 3477403 by norm_num,
    show ((46522597 / 50000000 : ℝ))⁻¹ = 50000000 / 46522597 by norm_num]
  ring

/-! ## The bridge -/

/-- **The `(0,2,2)` fine cell's entropy rate, times `tau`, is the published value.**

`tau * (mass * H(alphatilde_row) + ones * log q) = mass * log V(T_{0,2,2}, alphatilde)`, exactly.
The left side is `tau` times the logarithm of the merged fibre dimension per period; the right is
the logarithm of `dwz63Val022 ^ mass`.  Both are the same integer combination of `log 2`, `log 3`,
`log (10^8/3477403)` and `log (5 * 10^7/46522597)`. -/
theorem dwz63_tau_mul_rate_eq_alphaTilde_two :
    dwz63Tau * ((WordType.profileMass (dwz63AlphaTilde 2) : ℝ) *
        WordType.profileEntropyNats (dwz63AlphaTilde 2)
      + ((∑ p : PositiveWord CWBlock 1,
          dwz63AlphaTilde 2 p * cwWordMiddleCount 1 p : ℕ) : ℝ) * Real.log dwz63Q)
      = (WordType.profileMass (dwz63AlphaTilde 2) : ℝ) * dwz63LogVal022 := by
  have h6 : Real.log (dwz63Q : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show ((dwz63Q : ℕ) : ℝ) = 6 by norm_num [dwz63Q],
      show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [dwz63_profileMass_alphaTilde, dwz63_profileEntropyNats_alphaTilde_two,
    dwz63_middleCountSum_alphaTilde_two, h6, dwz63LogVal022, dwz63Tau, dwz63A]
  push_cast
  ring

/-- The `(2,0,2)` row is the same profile, so the same identity. -/
theorem dwz63_tau_mul_rate_eq_alphaTilde_nine :
    dwz63Tau * ((WordType.profileMass (dwz63AlphaTilde 9) : ℝ) *
        WordType.profileEntropyNats (dwz63AlphaTilde 9)
      + ((∑ p : PositiveWord CWBlock 1,
          dwz63AlphaTilde 9 p * cwWordMiddleCount 1 p : ℕ) : ℝ) * Real.log dwz63Q)
      = (WordType.profileMass (dwz63AlphaTilde 9) : ℝ) * dwz63LogVal022 := by
  rw [← dwz63AlphaTilde_two_eq_nine]
  exact dwz63_tau_mul_rate_eq_alphaTilde_two

/-- **The exponentiated form.**  `(2 ^ (mass * H) * q ^ ones) ^ tau = dwz63Val022 ^ mass`, with
`tau` outermost --- the shape `dwz63_exists_zeroFineCellWeight` produces. -/
theorem dwz63_entropyRate_rpow_tau_eq_val022_pow :
    ((2 : ℝ) ^ ((WordType.profileMass (dwz63AlphaTilde 2) : ℝ) *
          WordType.profileEntropyBits (dwz63AlphaTilde 2)) *
        ((dwz63Q : ℝ) ^ (∑ p : PositiveWord CWBlock 1,
          dwz63AlphaTilde 2 p * cwWordMiddleCount 1 p))) ^ dwz63Tau =
      dwz63Val022 ^ WordType.profileMass (dwz63AlphaTilde 2) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hq : (0 : ℝ) < (dwz63Q : ℝ) := by norm_num [dwz63Q]
  have hmass : (WordType.profileMass (dwz63AlphaTilde 2) : ℝ) *
      WordType.profileEntropyBits (dwz63AlphaTilde 2) =
      ((WordType.profileMass (dwz63AlphaTilde 2) : ℝ) *
        WordType.profileEntropyNats (dwz63AlphaTilde 2)) / Real.log 2 := by
    rw [WordType.profileEntropyBits]
    ring
  have htwo : (2 : ℝ) ^ ((WordType.profileMass (dwz63AlphaTilde 2) : ℝ) *
      WordType.profileEntropyBits (dwz63AlphaTilde 2)) =
      Real.exp ((WordType.profileMass (dwz63AlphaTilde 2) : ℝ) *
        WordType.profileEntropyNats (dwz63AlphaTilde 2)) := by
    rw [hmass, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp
  have hpow : ((dwz63Q : ℝ) ^ (∑ p : PositiveWord CWBlock 1,
      dwz63AlphaTilde 2 p * cwWordMiddleCount 1 p)) =
      Real.exp (((∑ p : PositiveWord CWBlock 1,
        dwz63AlphaTilde 2 p * cwWordMiddleCount 1 p : ℕ) : ℝ) * Real.log dwz63Q) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [htwo, hpow, ← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    dwz63Val022, ← Real.exp_nat_mul]
  rw [mul_comm _ dwz63Tau, dwz63_tau_mul_rate_eq_alphaTilde_two]

end AlgebraicComplexity.Examples
