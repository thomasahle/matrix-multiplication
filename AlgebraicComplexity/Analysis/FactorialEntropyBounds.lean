/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Factorial bounds for entropy estimates

This lightweight leaf contains the general Stirling inequalities shared by binary, ternary, and
arbitrary finite-alphabet method-of-types arguments.  It has no word-type or entropy-client import.
-/

namespace AlgebraicComplexity.WordType

open Real

/-- Stirling's upper bound with a square-root prefactor. -/
theorem factorial_le_exp_mul_sqrt_mul {n : ℕ} (hn : 0 < n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * √(n : ℝ) *
      ((n : ℝ) / Real.exp 1) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hseq : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  rw [Stirling.stirlingSeq_one] at hseq
  unfold Stirling.stirlingSeq at hseq
  have hden : 0 < √(2 * ((m + 1 : ℕ) : ℝ)) *
      (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by positivity
  apply (div_le_iff₀ hden).mp at hseq
  calc
    ((m + 1).factorial : ℝ) ≤
        (Real.exp 1 / √2) *
          (√(2 * ((m + 1 : ℕ) : ℝ)) *
            (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) := hseq
    _ = Real.exp 1 * √(((m + 1 : ℕ) : ℝ)) *
          (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
      rw [show √(2 * ((m + 1 : ℕ) : ℝ)) = √2 * √(((m + 1 : ℕ) : ℝ)) by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]]
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]

/-- A coarser Stirling upper bound with a linear prefactor. -/
theorem factorial_le_exp_mul_self_mul {n : ℕ} (hn : 0 < n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * (n : ℝ) *
      ((n : ℝ) / Real.exp 1) ^ n := by
  apply (factorial_le_exp_mul_sqrt_mul hn).trans
  gcongr
  exact Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hn))

/-- The exponential part of Stirling's formula is a global lower bound for a positive
factorial. -/
theorem pow_div_exp_le_factorial {n : ℕ} (hn : 0 < n) :
    (((n : ℝ) / Real.exp 1) ^ n) ≤ (n.factorial : ℝ) := by
  have hsqrt : 1 ≤ √(2 * Real.pi * (n : ℝ)) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_gt_three]
  calc
    ((n : ℝ) / Real.exp 1) ^ n ≤
        √(2 * Real.pi * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n := by
      exact le_mul_of_one_le_left (by positivity) hsqrt
    _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n

end AlgebraicComplexity.WordType
