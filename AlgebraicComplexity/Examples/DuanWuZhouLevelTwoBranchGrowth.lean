/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedHashBranch
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorRateBrick
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchLoss

set_option autoImplicit false

/-!
# The hashing branch exceeds one, and beats the batching loss

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]` §6.3 fixes the level-two parameters
(`papers/sources/2210.10173/global_value.tex:332-378`, `table:result-2nd`), from which the
committed rational bounds `dwz63XRate` and `dwz63HashLossMultiplier` are read; the asymmetric
hashing modulus they feed is the paragraph `:130-140`.

Two facts the hole side needs and the tree did not carry.  The first is that the hashing branch
`ᾱ_X / K` is **above one** --- the tree had only `dwz63HashingBranch_pos` and the upper bound
`dwz63HashingBranch_le_exp_entropyX`.  The second is that its powers eventually dominate the
batching loss, `2 · (5N + 1) · (2 · lossHash N) ≤ branch ^ N`: an exponential against a
subexponential times an affine factor.

Both are cofinal statements, matching the `∃ cutoff` shape the rest of this route uses; the
generic step is isolated as `dwz63_eventually_subexp_mul_affine_le_pow`, which is
`dwz63_eventually_subexponential_mul_pow_le_one` read at `r⁻¹`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

universe u

/-! ## The branch is above one -/

/-- **`1 < dwz63HashingBranch`.**  `dwz63XRate = 2.9718…` is a committed lower bound for
`exp dwz63EntropyX` (`dwz63_xRate_le_exp`) and `dwz63HashLossMultiplier = 1 + 10 ^ (-10)`, so the
quotient is above one by rational arithmetic. -/
theorem dwz63_one_lt_hashingBranch : 1 < dwz63HashingBranch := by
  have hK : (0 : ℝ) < dwz63HashLossMultiplier := dwz63HashLossMultiplier_pos
  have h1 : (1 : ℝ) < dwz63XRate / dwz63HashLossMultiplier := by
    rw [lt_div_iff₀ hK]
    unfold dwz63XRate dwz63HashLossMultiplier
    norm_num
  have h2 : dwz63XRate / dwz63HashLossMultiplier ≤ dwz63HashingBranch := by
    unfold dwz63HashingBranch
    gcongr
    exact dwz63_xRate_le_exp
  linarith

/-! ## Exponential beats subexponential times affine -/

/-- **A subexponential factor times an affine factor is eventually below any power `r ^ n` with
`1 < r`.**  This is `dwz63_eventually_subexponential_mul_pow_le_one` at ratio `r⁻¹`. -/
theorem dwz63_eventually_subexp_mul_affine_le_pow {slack : ℕ → ℝ} {r a b : ℝ}
    (hs : Growth.Subexponential slack) (hr : 1 < r) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → slack n * (a * (n : ℝ) + b) ≤ r ^ n := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hrne : r ≠ 0 := ne_of_gt hr0
  obtain ⟨N, hN⟩ := dwz63_eventually_subexponential_mul_pow_le_one
    (hs.mul (dwz63_subexponential_affine ha hb))
    (by positivity : (0 : ℝ) ≤ 1 / r)
    (by rw [div_lt_one hr0]; exact hr)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hkey : slack n * (a * (n : ℝ) + b) * (1 / r) ^ n ≤ 1 := hN n hn
  have hpow : (0 : ℝ) < r ^ n := pow_pos hr0 n
  have hinv : (1 / r) ^ n * r ^ n = 1 := by
    rw [← mul_pow, one_div, inv_mul_cancel₀ hrne, one_pow]
  calc slack n * (a * (n : ℝ) + b)
      = slack n * (a * (n : ℝ) + b) * ((1 / r) ^ n * r ^ n) := by rw [hinv, mul_one]
    _ = slack n * (a * (n : ℝ) + b) * (1 / r) ^ n * r ^ n := by ring
    _ ≤ 1 * r ^ n := mul_le_mul_of_nonneg_right hkey hpow.le
    _ = r ^ n := one_mul _

/-! ## The batching loss is eventually dominated -/

/-- **`hlarge` from `hbranch`, cofinally.**  At the joint-class loss
`dwz63PlainMarkedLossHashJoint` the batching requirement `2 · (5N + 1) · (2 · lossHash N)` is
eventually below `dwz63HashingBranch ^ N`: the branch is above one
(`dwz63_one_lt_hashingBranch`), the loss is subexponential
(`subexponential_dwz63PlainMarkedLossHashJoint`) and the batch size is affine in `N`. -/
theorem dwz63_eventually_hlarge_le_branch_pow (K : Type u) [CommRing K] :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 * (5 * (N : ℝ) + 1) * (2 * dwz63PlainMarkedLossHashJoint K N) ≤
        dwz63HashingBranch ^ N := by
  obtain ⟨N₀, hN₀⟩ := dwz63_eventually_subexp_mul_affine_le_pow
    (slack := fun N : ℕ ↦ 4 * dwz63PlainMarkedLossHashJoint K N)
    (r := dwz63HashingBranch) (a := 5) (b := 1)
    ((subexponential_dwz63PlainMarkedLossHashJoint K).const_mul (by norm_num))
    dwz63_one_lt_hashingBranch (by norm_num) (by norm_num)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have h := hN₀ N hN
  calc 2 * (5 * (N : ℝ) + 1) * (2 * dwz63PlainMarkedLossHashJoint K N)
      = 4 * dwz63PlainMarkedLossHashJoint K N * (5 * (N : ℝ) + 1) := by ring
    _ ≤ dwz63HashingBranch ^ N := h

end AlgebraicComplexity.Examples
