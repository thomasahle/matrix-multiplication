/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.HoleRepairGrowth

/-!
# Interface-tensor specialization of the hole-repair copy loss

This module instantiates the generic seven-branch growth lemmas of
`Analysis/HoleRepairGrowth.lean` at the concrete parameters of recursive interface tensors: an
interface leg at power `n` has at most `3 ^ n` parts, and every repair step shrinks the remaining
part count by a factor of at least `n + 2`.  The resulting common ceiling-log depth and its
explicit three-leg loss `7 ^ (3 * depth + 1)` are proved subexponential.

These constants are matrix-multiplication-shaped, so the module lives in the
matrix-multiplication theory layer; the depth-generic statements it consumes stay in the generic
analysis layer.  The declarations keep the `AlgebraicComplexity.HoleRepair` namespace of the
generic development they specialize.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity.Growth

/-- Common ceiling-log depth sufficient for any interface leg having at most `3^n` parts and a
per-step shrink base of at least `n + 2`. -/
def interfaceRepairDepth (n : ℕ) : ℕ :=
  Nat.clog (n + 2) (3 ^ n)

/-- Explicit three-leg seven-branch loss for the common interface depth. -/
def interfaceRepairLoss (n : ℕ) : ℝ :=
  (7 : ℝ) ^ (3 * interfaceRepairDepth n + 1)

/-- The explicit loss needed for repairing three legs of an interface tensor with at most `3^n`
parts is subexponential.

This proof is entirely discrete.  For a requested comparison base `δ > 1`, choose `L` with
`7 ≤ δ^L`.  Once `2^(6L) ≤ n+2`, ceiling-log monotonicity gives
`interfaceRepairDepth n ≤ ⌈2n/(6L)⌉`; the predecessor property of ceiling division then absorbs
the three depth coordinates into `δ^n`.  A single explicit constant covers the finite prefix. -/
theorem interfaceRepairLoss_subexponential :
    Subexponential interfaceRepairLoss := by
  refine ⟨fun n ↦ by unfold interfaceRepairLoss; positivity, ?_⟩
  intro δ hδ
  have hδpos : 0 < δ := zero_lt_one.trans hδ
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, (7 : ℝ) ≤ δ ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt hδ).eventually
      (Filter.eventually_ge_atTop 7)
  obtain ⟨ell₀, hell₀⟩ := hevent.exists
  let ell : ℕ := ell₀ + 1
  have hellPos : 0 < ell := by simp [ell]
  have hsevenDelta : (7 : ℝ) ≤ δ ^ ell := by
    calc
      (7 : ℝ) ≤ δ ^ ell₀ := hell₀
      _ ≤ δ ^ ell := by
        apply pow_le_pow_right₀ hδ.le
        simp [ell]
  let k : ℕ := 6 * ell
  have hkPos : 0 < k := mul_pos (by norm_num) hellPos
  let cutoff : ℕ := 2 ^ k
  have hcutoffPos : 0 < cutoff := by positivity
  let prefixBound : ℝ := (7 : ℝ) ^ (3 * (3 ^ cutoff) + 1)
  have hprefixPos : 0 < prefixBound := by positivity
  have honePrefix : 1 ≤ prefixBound := by
    exact one_le_pow₀ (by norm_num)
  let C : ℝ := (7 : ℝ) ^ 4 * prefixBound
  have hC : 0 < C := mul_pos (by positivity) hprefixPos
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : cutoff ≤ n
  · have hnPos : 0 < n := hcutoffPos.trans_le hn
    have hbase : 2 ^ k ≤ n + 2 := by
      exact hn.trans (Nat.le_add_right n 2)
    let q : ℕ := (2 * n) ⌈/⌉ k
    have hdepth : interfaceRepairDepth n ≤ q := by
      exact clog_add_two_three_pow_le_ceilDiv hkPos hbase
    have hqPos : 0 < q := by
      dsimp [q]
      by_contra hnot
      have hqZero : (2 * n) ⌈/⌉ k = 0 := Nat.eq_zero_of_not_pos hnot
      have hle : 2 * n ≤ k * 0 :=
        (ceilDiv_le_iff_le_mul hkPos).1 (show (2 * n) ⌈/⌉ k ≤ 0 by omega)
      omega
    have hmul : k * (q - 1) < 2 * n := by
      exact mul_pred_ceilDiv_lt (mul_pos (by norm_num) hnPos) hkPos
    have htwice : 2 * (3 * ell * (q - 1)) < 2 * n := by
      calc
        2 * (3 * ell * (q - 1)) = k * (q - 1) := by
          dsimp [k]
          ring
        _ < 2 * n := hmul
    have hsmall : 3 * ell * (q - 1) < n :=
      lt_of_mul_lt_mul_left htwice (by norm_num)
    have hdeltaExponent :
        (7 : ℝ) ^ (3 * (q - 1)) ≤ δ ^ n := by
      calc
        (7 : ℝ) ^ (3 * (q - 1)) ≤
            (δ ^ ell) ^ (3 * (q - 1)) :=
          pow_le_pow_left₀ (by norm_num) hsevenDelta _
        _ = δ ^ (3 * ell * (q - 1)) := by
          rw [← pow_mul]
          congr 1
          ring
        _ ≤ δ ^ n := pow_le_pow_right₀ hδ.le hsmall.le
    have hexponent :
        3 * interfaceRepairDepth n + 1 ≤ 3 * q + 1 := by omega
    have hqSplit : 3 * q + 1 = 4 + 3 * (q - 1) := by omega
    calc
      interfaceRepairLoss n = (7 : ℝ) ^ (3 * interfaceRepairDepth n + 1) := rfl
      _ ≤ (7 : ℝ) ^ (3 * q + 1) :=
        pow_le_pow_right₀ (by norm_num) hexponent
      _ = (7 : ℝ) ^ 4 * (7 : ℝ) ^ (3 * (q - 1)) := by
        rw [hqSplit, pow_add]
      _ ≤ (7 : ℝ) ^ 4 * δ ^ n :=
        mul_le_mul_of_nonneg_left hdeltaExponent (by positivity)
      _ ≤ C * δ ^ n := by
        dsimp [C]
        have hpowNonneg : 0 ≤ δ ^ n := pow_nonneg hδpos.le n
        have hsevenFour : 0 ≤ (7 : ℝ) ^ 4 := by positivity
        nlinarith [mul_nonneg hsevenFour hpowNonneg,
          mul_nonneg hprefixPos.le hpowNonneg]
  · have hnCutoff : n ≤ cutoff := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have hdepthSelf : interfaceRepairDepth n ≤ 3 ^ n := by
      apply Nat.clog_le_of_le_pow
      exact (Nat.lt_pow_self (show 1 < n + 2 by omega)).le
    have hthree : 3 ^ n ≤ 3 ^ cutoff :=
      Nat.pow_le_pow_right (by omega) hnCutoff
    have hexponent :
        3 * interfaceRepairDepth n + 1 ≤ 3 * (3 ^ cutoff) + 1 := by omega
    calc
      interfaceRepairLoss n = (7 : ℝ) ^ (3 * interfaceRepairDepth n + 1) := rfl
      _ ≤ prefixBound := by
        dsimp [prefixBound]
        exact pow_le_pow_right₀ (by norm_num) hexponent
      _ ≤ C := by
        dsimp [C]
        exact le_mul_of_one_le_left hprefixPos.le (one_le_pow₀ (by norm_num))
      _ ≤ C * δ ^ n :=
        le_mul_of_one_le_right hC.le (one_le_pow₀ hδ.le)

end AlgebraicComplexity.HoleRepair
