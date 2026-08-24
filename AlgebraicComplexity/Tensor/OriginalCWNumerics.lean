import Mathlib

set_option linter.style.header false

/-!
# Exact numerical inequality for the original Coppersmith--Winograd parameters

The historical tensor-square analysis uses `q = 6`.  We work at the rounded exponent `ρ = 2.376`
and with the rational parameters printed in the classical analysis.  Every logarithmic lower bound
below follows from an exact power inequality and monotonicity of the real logarithm.
-/

namespace AlgebraicComplexity.OriginalCW

/-- Base-two logarithm, expressed through Mathlib's natural logarithm. -/
noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- A lower bound on `log₂ x` obtained from `2^m < x^n`. -/
theorem log2_lower_of_pow_lt
    (x : ℝ) (m n : ℕ) (hx : 0 < x) (hn : 0 < n)
    (hpow : (2 : ℝ) ^ m < x ^ n) :
    (m : ℝ) / n < log2 x := by
  have hlogpow : Real.log ((2 : ℝ) ^ m) < Real.log (x ^ n) := by
    exact Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [log2, div_lt_div_iff₀ hnR hlog2]
  nlinarith

private theorem log2_six_lower : (137 : ℝ) / 53 < log2 6 := by
  have hq : (2 : ℚ) ^ 137 < 6 ^ 53 := by norm_num
  have hr : (2 : ℝ) ^ 137 < 6 ^ 53 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt 6 137 53 (by positivity) (by norm_num) hr

private theorem log2_twelve_lower : (190 : ℝ) / 53 < log2 12 := by
  have hq : (2 : ℚ) ^ 190 < 12 ^ 53 := by norm_num
  have hr : (2 : ℝ) ^ 190 < 12 ^ 53 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt 12 190 53 (by positivity) (by norm_num) hr

private theorem log2_thirtyEight_lower : (509 : ℝ) / 97 < log2 38 := by
  have hq : (2 : ℚ) ^ 509 < 38 ^ 97 := by norm_num
  have hr : (2 : ℝ) ^ 509 < 38 ^ 97 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt 38 509 97 (by positivity) (by norm_num) hr

private theorem log2_inv_b1_lower :
    (581 : ℝ) / 94 < log2 ((50000 : ℝ) / 689) := by
  have hq : (2 : ℚ) ^ 581 < ((50000 : ℚ) / 689) ^ 94 := by norm_num
  have hr : (2 : ℝ) ^ 581 < ((50000 : ℝ) / 689) ^ 94 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt ((50000 : ℝ) / 689) 581 94
    (by positivity) (by norm_num) hr

private theorem log2_inv_two_b2_lower :
    (1 : ℝ) / 25 < log2 ((25000 : ℝ) / 24311) := by
  have hq : (2 : ℚ) ^ 1 < ((25000 : ℚ) / 24311) ^ 25 := by norm_num
  have hr : (2 : ℝ) ^ 1 < ((25000 : ℝ) / 24311) ^ 25 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt ((25000 : ℝ) / 24311) 1 25
    (by positivity) (by norm_num) hr

private theorem log2_inv_a1_lower :
    (1124 : ℝ) / 93 < log2 ((100000 : ℝ) / 23) := by
  have hq : (2 : ℚ) ^ 1124 < ((100000 : ℚ) / 23) ^ 93 := by norm_num
  have hr : (2 : ℝ) ^ 1124 < ((100000 : ℝ) / 23) ^ 93 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt ((100000 : ℝ) / 23) 1124 93
    (by positivity) (by norm_num) hr

private theorem log2_inv_two_a2_lower : (463 : ℝ) / 87 < log2 40 := by
  have hq : (2 : ℚ) ^ 463 < 40 ^ 87 := by norm_num
  have hr : (2 : ℝ) ^ 463 < 40 ^ 87 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt 40 463 87 (by positivity) (by norm_num) hr

private theorem log2_inv_two_a3_a4_lower :
    (104 : ℝ) / 81 < log2 ((300000 : ℝ) / 123193) := by
  have hq : (2 : ℚ) ^ 104 < ((300000 : ℚ) / 123193) ^ 81 := by norm_num
  have hr : (2 : ℝ) ^ 104 < ((300000 : ℝ) / 123193) ^ 81 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt ((300000 : ℝ) / 123193) 104 81
    (by positivity) (by norm_num) hr

private theorem log2_inv_two_a2_two_a4_lower :
    (79 : ℝ) / 66 < log2 ((150000 : ℝ) / 65419) := by
  have hq : (2 : ℚ) ^ 79 < ((150000 : ℚ) / 65419) ^ 66 := by norm_num
  have hr : (2 : ℝ) ^ 79 < ((150000 : ℝ) / 65419) ^ 66 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt ((150000 : ℝ) / 65419) 79 66
    (by positivity) (by norm_num) hr

private theorem log2_inv_two_a1_two_a2_a3_lower :
    (86 : ℝ) / 29 < log2 ((125 : ℝ) / 16) := by
  have hq : (2 : ℚ) ^ 86 < ((125 : ℚ) / 16) ^ 29 := by norm_num
  have hr : (2 : ℝ) ^ 86 < ((125 : ℝ) / 16) ^ 29 := by exact_mod_cast hq
  exact log2_lower_of_pow_lt ((125 : ℝ) / 16) 86 29
    (by positivity) (by norm_num) hr

/-- The inner `(2,1,1)` logarithmic value lower bound from the published parameters. -/
noncomputable def innerLogLower : ℝ :=
  ((297 : ℝ) / 125 / 3) *
      (2 * ((689 : ℝ) / 50000) + 4 * ((24311 : ℝ) / 50000)) * log2 6 +
    (1 / 3 : ℝ) *
      (2 * ((689 : ℝ) / 50000) * log2 ((50000 : ℝ) / 689) +
       2 * ((24311 : ℝ) / 50000) * log2 ((25000 : ℝ) / 24311) + 2)

/-- The outer tensor-square logarithmic value lower bound. -/
noncomputable def squareLogLower : ℝ :=
  2 * ((1 : ℝ) / 80) * ((297 : ℝ) / 125) * log2 12 +
  ((5127 : ℝ) / 50000) * ((297 : ℝ) / 125) * log2 38 +
  3 * ((61669 : ℝ) / 300000) * innerLogLower +
  ((23 : ℝ) / 100000) * log2 ((100000 : ℝ) / 23) +
  2 * ((1 : ℝ) / 80) * log2 40 +
  ((123193 : ℝ) / 300000) * log2 ((300000 : ℝ) / 123193) +
  ((65419 : ℝ) / 150000) * log2 ((150000 : ℝ) / 65419) +
  ((16 : ℝ) / 125) * log2 ((125 : ℝ) / 16)

/-- A completely rational lower approximation to `squareLogLower`. -/
def squareLogRationalLower : ℚ :=
  2177553840764452827683357 / 362897628080625000000000

/-- The rational approximation has visible positive slack over six. -/
theorem squareLogRationalLower_gt_six :
    (6 : ℚ) < squareLogRationalLower := by
  norm_num [squareLogRationalLower]

/-- The exact logarithmic expression is above the rational approximation. -/
theorem squareLogLower_gt_rational :
    (squareLogRationalLower : ℝ) < squareLogLower := by
  have h6 := log2_six_lower
  have h12 := log2_twelve_lower
  have h38 := log2_thirtyEight_lower
  have hb1 := log2_inv_b1_lower
  have hb2 := log2_inv_two_b2_lower
  have ha1 := log2_inv_a1_lower
  have ha2 := log2_inv_two_a2_lower
  have ha34 := log2_inv_two_a3_a4_lower
  have ha24 := log2_inv_two_a2_two_a4_lower
  have ha123 := log2_inv_two_a1_two_a2_a3_lower
  norm_num [squareLogLower, innerLogLower, squareLogRationalLower] at *
  nlinarith

/-- The original tensor-square logarithmic lower bound exceeds `log₂ 64 = 6`. -/
theorem squareLogLower_gt_six : 6 < squareLogLower := by
  have hrat : (6 : ℝ) < (squareLogRationalLower : ℝ) := by
    exact_mod_cast squareLogRationalLower_gt_six
  exact hrat.trans squareLogLower_gt_rational

#print axioms squareLogLower_gt_six

end AlgebraicComplexity.OriginalCW
