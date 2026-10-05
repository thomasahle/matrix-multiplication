/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.Combinatorics.HoleRepair

/-!
# Asymptotic growth of recursive hole repair

This module joins the exact seven-branch recurrence in `Combinatorics.HoleRepair` to the generic
subexponential-rate API.  The tensor argument only has to provide integer repair depths bounded by
`O(n / log n)`; the lemmas below then remove the resulting copy loss from the final exponent.

Every statement here is generic in the depth sequence.  The specialization to the concrete
interface-tensor part counts and shrink bases used by matrix-multiplication clients lives one
layer up, in `MatrixMultiplication/InterfaceRepairGrowth.lean`.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity.Growth

/-- A seven-ary tree whose integer depth is bounded by `a n / log (n+2)` has subexponential
size. -/
theorem sevenPow_depth_subexponential
    (depth : ℕ → ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hdepth : ∀ n,
      (depth n : ℝ) ≤ a * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ))) :
    Subexponential (fun n ↦ (7 : ℝ) ^ depth n) := by
  have hlogSeven : 0 ≤ Real.log 7 := (Real.log_pos (by norm_num)).le
  have hmajorant :=
    Subexponential.exp_mul_natCast_div_log_add_two (mul_nonneg hlogSeven ha)
  apply hmajorant.mono
  · intro n
    positivity
  · intro n
    have hexponent :
        (depth n : ℝ) * Real.log 7 ≤
          (Real.log 7 * a) * (n : ℝ) /
            Real.log (((n + 2 : ℕ) : ℝ)) := by
      calc
        (depth n : ℝ) * Real.log 7 ≤
            (a * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ))) * Real.log 7 :=
          mul_le_mul_of_nonneg_right (hdepth n) hlogSeven
        _ = (Real.log 7 * a) * (n : ℝ) /
            Real.log (((n + 2 : ℕ) : ℝ)) := by ring
    calc
      (7 : ℝ) ^ depth n = Real.exp ((depth n : ℝ) * Real.log 7) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp ((Real.log 7 * a) * (n : ℝ) /
          Real.log (((n + 2 : ℕ) : ℝ))) := Real.exp_le_exp.mpr hexponent

/-- The exact paper-style bound `7^(1 + depth)` is still subexponential. -/
theorem sevenPow_succ_depth_subexponential
    (depth : ℕ → ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hdepth : ∀ n,
      (depth n : ℝ) ≤ a * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ))) :
    Subexponential (fun n ↦ (7 : ℝ) ^ (depth n + 1)) := by
  have h := (sevenPow_depth_subexponential depth ha hdepth).const_mul
    (show (0 : ℝ) ≤ 7 by norm_num)
  simpa only [pow_succ, mul_comm] using h

/-- Three independently certified repair depths give the full three-leg copy loss from the
recursive hole-repair theorem. -/
theorem sevenPow_threeDepths_subexponential
    (depthX depthY depthZ : ℕ → ℕ)
    {aX aY aZ : ℝ} (haX : 0 ≤ aX) (haY : 0 ≤ aY) (haZ : 0 ≤ aZ)
    (hdepthX : ∀ n,
      (depthX n : ℝ) ≤ aX * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ)))
    (hdepthY : ∀ n,
      (depthY n : ℝ) ≤ aY * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ)))
    (hdepthZ : ∀ n,
      (depthZ n : ℝ) ≤ aZ * (n : ℝ) / Real.log (((n + 2 : ℕ) : ℝ))) :
    Subexponential
      (fun n ↦ (7 : ℝ) ^ (depthX n + depthY n + depthZ n + 1)) := by
  have hX := sevenPow_depth_subexponential depthX haX hdepthX
  have hY := sevenPow_depth_subexponential depthY haY hdepthY
  have hZ := sevenPow_depth_subexponential depthZ haZ hdepthZ
  have h := ((hX.mul hY).mul hZ).const_mul (show (0 : ℝ) ≤ 7 by norm_num)
  simpa only [pow_add, pow_one, mul_assoc, mul_comm, mul_left_comm] using h

end AlgebraicComplexity.HoleRepair
