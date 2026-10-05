import AlgebraicComplexity.Analysis.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified logarithm bounds

The paper bounds logarithms with the atanh series

`log ((1+x)/(1-x)) = 2 * ∑ k, x^(2k+1)/(2k+1)`.

Mathlib already proves rigorous lower and upper remainder estimates for this series.  Here those
theorems are specialized to `log 2` and `log (7/4)`, with twenty rational terms.  This is enough to
prove the paper's very tight decimal enclosure `8 log₂ 7 < 22.45883937646084` without trusting a
floating-point interval endpoint.
-/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.LogBounds

open AlgebraicComplexity.Analysis

/-- Twenty terms leave ample room below the printed decimal endpoint. -/
def seriesSteps : ℕ := 20

def logTwoLower : ℝ :=
  2 * atanhPartial (1 / 3) seriesSteps

def logTwoUpper : ℝ :=
  2 * (atanhPartial (1 / 3) seriesSteps + atanhRemainder (1 / 3) seriesSteps)

def logSevenFourthsUpper : ℝ :=
  2 * (atanhPartial (3 / 11) seriesSteps + atanhRemainder (3 / 11) seriesSteps)

def logSevenUpper : ℝ :=
  logSevenFourthsUpper + 2 * logTwoUpper

/-- Simple rational lower endpoint for `1 / log 2`, used by quadratic KL certificates. -/
def inverseLogTwoLower : ℝ := 721 / 500

/-- The exact rational represented by the paper's printed upper endpoint. -/
def rankBudgetUpper : ℝ := 22.45883937646084

/-- The rational lower enclosure for `log 2` is strictly positive.

Proof sketch: its atanh partial sum is nonempty and has positive argument, so positivity follows
structurally from the zeroth summand rather than by expanding all twenty rational terms. -/
theorem logTwoLower_pos : 0 < logTwoLower := by
  exact mul_pos (by norm_num) <|
    atanhPartial_pos (by norm_num) (by norm_num [seriesSteps])

theorem logTwoLower_le_logTwo : logTwoLower ≤ Real.log 2 := by
  have h := atanhPartial_le_halfLogRatio (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
    seriesSteps
  rw [show ((1 + (1 / 3 : ℝ)) / (1 - 1 / 3)) = 2 by norm_num] at h
  rw [logTwoLower]
  linarith

theorem logTwo_le_logTwoUpper : Real.log 2 ≤ logTwoUpper := by
  have h := halfLogRatio_le_atanhPartial_add_remainder
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) seriesSteps
  rw [show ((1 + (1 / 3 : ℝ)) / (1 - 1 / 3)) = 2 by norm_num] at h
  rw [logTwoUpper]
  linarith

/-- Directed rational enclosure for the only transcendental factor in the quadratic parent
correction. -/
theorem inverseLogTwoLower_le_inv_logTwo :
    inverseLogTwoLower ≤ (Real.log 2)⁻¹ := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : logTwoUpper < (500 / 721 : ℝ) := by
    norm_num [logTwoUpper, atanhPartial, atanhRemainder, seriesSteps]
  have hlogUpper : Real.log 2 < (500 / 721 : ℝ) :=
    logTwo_le_logTwoUpper.trans_lt hupper
  rw [inverseLogTwoLower, inv_eq_one_div]
  apply (le_div_iff₀ hlogTwoPos).2
  norm_num at hlogUpper ⊢
  nlinarith

theorem logSevenFourths_le_upper : Real.log (7 / 4 : ℝ) ≤ logSevenFourthsUpper := by
  have h := halfLogRatio_le_atanhPartial_add_remainder
    (x := (3 / 11 : ℝ)) (by norm_num) (by norm_num) seriesSteps
  rw [show ((1 + (3 / 11 : ℝ)) / (1 - 3 / 11)) = 7 / 4 by norm_num] at h
  rw [logSevenFourthsUpper]
  linarith

theorem logSeven_decompose :
    Real.log 7 = Real.log (7 / 4 : ℝ) + 2 * Real.log 2 := by
  calc
    Real.log 7 = Real.log ((7 / 4 : ℝ) * 4) := by norm_num
    _ = Real.log (7 / 4 : ℝ) + Real.log 4 := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
    _ = Real.log (7 / 4 : ℝ) + 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring

theorem logSeven_le_logSevenUpper : Real.log 7 ≤ logSevenUpper := by
  rw [logSeven_decompose, logSevenUpper]
  linarith [logSevenFourths_le_upper, logTwo_le_logTwoUpper]

/-- Pure rational arithmetic showing that the two series enclosures fit inside the endpoint. -/
theorem rational_rankBudget_separation :
    8 * logSevenUpper < rankBudgetUpper * logTwoLower := by
  norm_num [logSevenUpper, logSevenFourthsUpper, logTwoUpper, logTwoLower,
    atanhPartial, atanhRemainder, seriesSteps, rankBudgetUpper]

/-- The rank budget enclosure used in the final certificate, proved analytically in Lean. -/
theorem eight_logTwo_seven_lt_rankBudgetUpper :
    8 * (Real.log 7 / Real.log 2) < rankBudgetUpper := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hleft : 8 * Real.log 7 ≤ 8 * logSevenUpper := by
    nlinarith [logSeven_le_logSevenUpper]
  have hright : rankBudgetUpper * logTwoLower ≤ rankBudgetUpper * Real.log 2 := by
    have hbudgetPos : 0 < rankBudgetUpper := by norm_num [rankBudgetUpper]
    exact mul_le_mul_of_nonneg_left logTwoLower_le_logTwo hbudgetPos.le
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hlogTwoPos).2
  nlinarith [rational_rankBudget_separation]

/-- The paper's stated 25-term full-log tail at the worst reduced argument `z = 1/3`. -/
def paperLogTail : ℝ :=
  (2 * (1 / 3 : ℝ) ^ 51 / (51 * (1 - (1 / 3 : ℝ) ^ 2))) / Real.log 2

theorem twoThirds_le_logTwo : (2 / 3 : ℝ) ≤ Real.log 2 := by
  have h := atanhPartial_le_halfLogRatio (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 1
  rw [show ((1 + (1 / 3 : ℝ)) / (1 - 1 / 3)) = 2 by norm_num] at h
  norm_num [atanhPartial] at h ⊢
  linarith

theorem paperLogTail_lt_twoEminus24 : paperLogTail < (2 / 10 ^ 24 : ℝ) := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [paperLogTail]
  apply (div_lt_iff₀ hlogTwoPos).2
  have hrational :
      2 * (1 / 3 : ℝ) ^ 51 / (51 * (1 - (1 / 3 : ℝ) ^ 2)) <
        (2 / 10 ^ 24 : ℝ) * (2 / 3) := by
    norm_num
  nlinarith [twoThirds_le_logTwo]

/-- Higham's nonnegative-arithmetic factor for at most `2^21` rounded operations. -/
def gammaTwoPow21 : ℝ :=
  ((2 : ℝ) ^ 21 / 2 ^ 53) / (1 - (2 : ℝ) ^ 21 / 2 ^ 53)

theorem gammaTwoPow21_lt_structuralReserveDiv200 :
    gammaTwoPow21 < ((1 : ℝ) / 2 ^ 24) / 200 := by
  norm_num [gammaTwoPow21]

end MatrixMultiplication.LogBounds
