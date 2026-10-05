/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Entropy

/-!
# Entropy decreases under deterministic observation

This file proves the elementary data-processing inequality for the repository's finite
`ProbabilityVector`: pushing a law forward along a deterministic map cannot increase Shannon
entropy.  The proof is self-contained and zero-safe.  It first proves subadditivity of
`Real.negMulLog` on nonnegative inputs, extends this to finite sums, and applies the result to every
fiber of the map.

The theorem is deliberately separate from KL divergence.  Type-counting and typed-leaf clients
often need only this monotonicity fact and should not have to import the heavier information-theory
layer.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

/-- Merging two nonnegative masses cannot increase their total Shannon contribution.

Proof sketch: when both masses are positive, monotonicity of `log` gives
`x log x + y log y ≤ (x+y) log (x+y)`; negating is the desired inequality.  If either mass is zero,
the statement is an identity. -/
theorem negMulLog_add_le_add_negMulLog {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp
  rcases hy.eq_or_lt with rfl | hypos
  · simp
  have hxs : Real.log x ≤ Real.log (x + y) :=
    Real.log_le_log hxpos (by linarith)
  have hys : Real.log y ≤ Real.log (x + y) :=
    Real.log_le_log hypos (by linarith)
  rw [Real.negMulLog_eq_neg]
  have hxmul := mul_le_mul_of_nonneg_left hxs hx
  have hymul := mul_le_mul_of_nonneg_left hys hy
  have hsum : x * Real.log x + y * Real.log y ≤
      (x + y) * Real.log (x + y) := by
    calc
      x * Real.log x + y * Real.log y ≤
          x * Real.log (x + y) + y * Real.log (x + y) :=
        add_le_add hxmul hymul
      _ = (x + y) * Real.log (x + y) := by ring
  calc
    -((x + y) * Real.log (x + y)) ≤
        -(x * Real.log x + y * Real.log y) := neg_le_neg hsum
    _ = -(x * Real.log x) + -(y * Real.log y) := by ring

/-- Merging any finite family of nonnegative masses cannot increase its total Shannon
contribution. -/
theorem negMulLog_sum_le_sum_negMulLog
    {I : Type u} (s : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.negMulLog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (negMulLog_add_le_add_negMulLog (hf i (by simp))
        (Finset.sum_nonneg fun j hj ↦ hf j (by simp [hj]))).trans
          (add_le_add (le_refl _) (ih (fun j hj ↦ hf j (by simp [hj]))))

namespace ProbabilityVector

variable {I : Type u} [Fintype I]

/-- Every coordinate of a finite probability vector is at most one. -/
theorem weight_le_one (p : ProbabilityVector I) (i : I) : p.weight i ≤ 1 := by
  rw [← p.total]
  exact Finset.single_le_sum (fun j _ ↦ p.nonneg j) (Finset.mem_univ i)

/-- Shannon entropy of a finite probability vector is nonnegative. -/
theorem entropy_nonneg (p : ProbabilityVector I) : 0 ≤ p.entropy := by
  unfold entropy
  exact Finset.sum_nonneg fun i _ ↦
    Real.negMulLog_nonneg (p.nonneg i) (p.weight_le_one i)

/-- A deterministic finite observation cannot increase Shannon entropy.

Proof sketch: for each output symbol, apply `negMulLog_sum_le_sum_negMulLog` to the masses in its
fiber.  Summing over output symbols and exchanging the two finite sums counts the contribution of
each source symbol exactly once. -/
theorem entropy_pushforward_le
    {J : Type v} [Fintype J] [DecidableEq J]
    (p : ProbabilityVector I) (f : I → J) :
    (p.pushforward f).entropy ≤ p.entropy := by
  classical
  unfold entropy
  simp only [pushforward_weight]
  calc
    (∑ j, Real.negMulLog (∑ i, if f i = j then p.weight i else 0)) ≤
        ∑ j, ∑ i, Real.negMulLog (if f i = j then p.weight i else 0) := by
      apply Finset.sum_le_sum
      intro j _
      exact negMulLog_sum_le_sum_negMulLog Finset.univ
        (fun i ↦ if f i = j then p.weight i else 0)
        (fun i _ ↦ by
          by_cases h : f i = j
          · simpa only [if_pos h] using p.nonneg i
          · simp only [if_neg h, le_refl])
    _ = ∑ i, Real.negMulLog (p.weight i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [apply_ite, Real.negMulLog_zero]
      rw [Finset.sum_eq_single (f i)]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp

/-- The same deterministic data-processing inequality in bits. -/
theorem entropyBits_pushforward_le
    {J : Type v} [Fintype J] [DecidableEq J]
    (p : ProbabilityVector I) (f : I → J) :
    (p.pushforward f).entropyBits ≤ p.entropyBits := by
  unfold entropyBits
  exact div_le_div_of_nonneg_right (p.entropy_pushforward_le f)
    (Real.log_pos (by norm_num)).le

end ProbabilityVector

end AlgebraicComplexity
