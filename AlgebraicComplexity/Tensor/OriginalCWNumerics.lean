import Mathlib

set_option linter.style.header false

/-!
# Exact numerical inequality for the original Coppersmith--Winograd parameters

The historical tensor-square analysis uses `q = 6`. We work internally at `ρ = 2.3759`, strictly
below the rounded headline `2.376`, and with rational parameters from the classical analysis. Every
logarithmic lower bound follows from an exact natural-number power inequality and monotonicity of
the real logarithm.
-/

namespace AlgebraicComplexity.OriginalCW

/-- The exponent used by the formal numerical certificate. -/
def rho : ℚ := 23759 / 10000

/-- The rounded historical headline. -/
def roundedTarget : ℚ := 297 / 125

/-- The internal endpoint is strictly below the rounded headline. -/
theorem rho_lt_roundedTarget : rho < roundedTarget := by
  norm_num [rho, roundedTarget]

/-- Base-two logarithm, expressed through Mathlib's natural logarithm. -/
noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- A lower bound on `log₂ x` obtained from `2^m < x^n`. -/
theorem log2_lower_of_pow_lt
    (x : ℝ) (m n : ℕ) (hn : 0 < n)
    (hpow : (2 : ℝ) ^ m < x ^ n) :
    (m : ℝ) / n < log2 x := by
  have hlogpow : Real.log ((2 : ℝ) ^ m) < Real.log (x ^ n) := by
    exact Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [log2, div_lt_div_iff₀ hnR hlog2]
  nlinarith

/-- Cast an exact natural-number power inequality to the reals. -/
private theorem two_pow_lt_nat_pow_of_nat
    (a m n : ℕ) (h : 2 ^ m < a ^ n) :
    (2 : ℝ) ^ m < (a : ℝ) ^ n := by
  exact_mod_cast h

/-- Convert a cross-multiplied natural-number inequality into a real rational-power inequality. -/
private theorem two_pow_lt_div_pow_of_nat
    (a b m n : ℕ) (hb : 0 < b)
    (h : 2 ^ m * b ^ n < a ^ n) :
    (2 : ℝ) ^ m < ((a : ℝ) / b) ^ n := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_pow, lt_div_iff₀ (pow_pos hbR n)]
  exact_mod_cast h

private theorem log2_six_lower : (137 : ℝ) / 53 < log2 6 := by
  have hnat : (2 : ℕ) ^ 137 < 6 ^ 53 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt 6 137 53 (by norm_num)
    (two_pow_lt_nat_pow_of_nat 6 137 53 hnat)

private theorem log2_twelve_lower : (190 : ℝ) / 53 < log2 12 := by
  have hnat : (2 : ℕ) ^ 190 < 12 ^ 53 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt 12 190 53 (by norm_num)
    (two_pow_lt_nat_pow_of_nat 12 190 53 hnat)

private theorem log2_thirtyEight_lower : (509 : ℝ) / 97 < log2 38 := by
  have hnat : (2 : ℕ) ^ 509 < 38 ^ 97 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt 38 509 97 (by norm_num)
    (two_pow_lt_nat_pow_of_nat 38 509 97 hnat)

private theorem log2_inv_b1_lower :
    (581 : ℝ) / 94 < log2 ((50000 : ℝ) / 689) := by
  have hnat : (2 : ℕ) ^ 581 * 689 ^ 94 < 50000 ^ 94 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt ((50000 : ℝ) / 689) 581 94 (by norm_num)
    (two_pow_lt_div_pow_of_nat 50000 689 581 94 (by norm_num) hnat)

private theorem log2_inv_two_b2_lower :
    (1 : ℝ) / 25 < log2 ((25000 : ℝ) / 24311) := by
  have hnat : (2 : ℕ) ^ 1 * 24311 ^ 25 < 25000 ^ 25 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  simpa using log2_lower_of_pow_lt ((25000 : ℝ) / 24311) 1 25 (by norm_num)
    (two_pow_lt_div_pow_of_nat 25000 24311 1 25 (by norm_num) hnat)

private theorem log2_inv_a1_lower :
    (1124 : ℝ) / 93 < log2 ((100000 : ℝ) / 23) := by
  have hnat : (2 : ℕ) ^ 1124 * 23 ^ 93 < 100000 ^ 93 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt ((100000 : ℝ) / 23) 1124 93 (by norm_num)
    (two_pow_lt_div_pow_of_nat 100000 23 1124 93 (by norm_num) hnat)

private theorem log2_inv_two_a2_lower : (463 : ℝ) / 87 < log2 40 := by
  have hnat : (2 : ℕ) ^ 463 < 40 ^ 87 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt 40 463 87 (by norm_num)
    (two_pow_lt_nat_pow_of_nat 40 463 87 hnat)

private theorem log2_inv_two_a3_a4_lower :
    (104 : ℝ) / 81 < log2 ((300000 : ℝ) / 123193) := by
  have hnat : (2 : ℕ) ^ 104 * 123193 ^ 81 < 300000 ^ 81 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt ((300000 : ℝ) / 123193) 104 81 (by norm_num)
    (two_pow_lt_div_pow_of_nat 300000 123193 104 81 (by norm_num) hnat)

private theorem log2_inv_two_a2_two_a4_lower :
    (79 : ℝ) / 66 < log2 ((150000 : ℝ) / 65419) := by
  have hnat : (2 : ℕ) ^ 79 * 65419 ^ 66 < 150000 ^ 66 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt ((150000 : ℝ) / 65419) 79 66 (by norm_num)
    (two_pow_lt_div_pow_of_nat 150000 65419 79 66 (by norm_num) hnat)

private theorem log2_inv_two_a1_two_a2_a3_lower :
    (86 : ℝ) / 29 < log2 ((125 : ℝ) / 16) := by
  have hnat : (2 : ℕ) ^ 86 * 16 ^ 29 < 125 ^ 29 := by
    set_option maxRecDepth 100000 in
    set_option exponentiation.threshold 2000 in
      decide
  exact log2_lower_of_pow_lt ((125 : ℝ) / 16) 86 29 (by norm_num)
    (two_pow_lt_div_pow_of_nat 125 16 86 29 (by norm_num) hnat)

/-- The inner `(2,1,1)` logarithmic value lower bound from the published parameters. -/
noncomputable def innerLogLower : ℝ :=
  ((rho : ℝ) / 3) *
      (2 * ((689 : ℝ) / 50000) + 4 * ((24311 : ℝ) / 50000)) * log2 6 +
    (1 / 3 : ℝ) *
      (2 * ((689 : ℝ) / 50000) * log2 ((50000 : ℝ) / 689) +
       2 * ((24311 : ℝ) / 50000) * log2 ((25000 : ℝ) / 24311) + 2)

/-- The outer tensor-square logarithmic value lower bound. -/
noncomputable def squareLogLower : ℝ :=
  2 * ((1 : ℝ) / 80) * (rho : ℝ) * log2 12 +
  ((5127 : ℝ) / 50000) * (rho : ℝ) * log2 38 +
  3 * ((61669 : ℝ) / 300000) * innerLogLower +
  ((23 : ℝ) / 100000) * log2 ((100000 : ℝ) / 23) +
  2 * ((1 : ℝ) / 80) * log2 40 +
  ((123193 : ℝ) / 300000) * log2 ((300000 : ℝ) / 123193) +
  ((65419 : ℝ) / 150000) * log2 ((150000 : ℝ) / 65419) +
  ((16 : ℝ) / 125) * log2 ((125 : ℝ) / 16)

/-- A completely rational lower approximation to `squareLogLower`. -/
def squareLogRationalLower : ℚ :=
  87099721094856335363013707 / 14515905123225000000000000

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
  norm_num [squareLogLower, innerLogLower, squareLogRationalLower, rho] at *
  nlinarith

/-- The original tensor-square logarithmic lower bound exceeds `log₂ 64 = 6`. -/
theorem squareLogLower_gt_six : 6 < squareLogLower := by
  have hrat : (6 : ℝ) < (squareLogRationalLower : ℝ) := by
    exact_mod_cast squareLogRationalLower_gt_six
  exact hrat.trans squareLogLower_gt_rational

#print axioms rho_lt_roundedTarget
#print axioms squareLogLower_gt_six

end AlgebraicComplexity.OriginalCW
