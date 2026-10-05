/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSharpFiberBound

/-!
# The hashing branch against `N_X`, loss-free

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoIntegrationMarkedFamily.lean`
consumes the marked-count rate

`hrate : dwz63HashingBranch ^ (6 (N)) * dwz63SharpRetentionLoss degree ≤ lossHash N * #marked`.

This module discharges the exponential half of it and isolates what remains.

## Why the declared rational is the wrong lower bound here

The obvious route is `dwz63_xRate_pow_le_dwz63XTypicalCount`, the estimate (b) form:
`dwz63XRate ^ (6 (n+1)) ≤ N_X`.  It does **not** suffice.  The hashing branch is
`Real.exp dwz63EntropyX / dwz63HashLossMultiplier` with `dwz63HashLossMultiplier = 1 + 10⁻¹⁰`, so
it sits `≈ 2.97 · 10⁻¹⁰` below `alphabar_X = exp H_X ≈ 2.9718193769565`, while the declared
rational `dwz63XRate = 2.9718193739847` sits `≈ 2.97 · 10⁻⁹` below it --- a full order of
magnitude further down.  So `dwz63HashingBranch > dwz63XRate`, and the ratio raised to `6 N` is
exponentially large: the rational route loses the branch.

The fix costs nothing.  `WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass` is
**loss-free after a cutoff** for *every* base strictly below the profile's own rate, and the
hashing branch is such a base for the single reason that `dwz63HashLossMultiplier > 1`.  Applying
it at `lowerBase := dwz63HashingBranch ^ (10 ^ 8)` gives
`dwz63HashingBranch ^ (6 (n+1)) ≤ N_X` outright, with no loss factor and no numerical enclosure of
`exp dwz63EntropyX` beyond the committed `profileEntropyNats_dwz63AlphaX`.

## What remains of `hrate`

`dwz63_hrate_of_retentionLoss_le` reduces the obligation to

`N_X * dwz63SharpRetentionLoss degree ≤ lossHash N * #marked`,

which is where `[DuanWuZhou2022]`'s cancellation happens: at
`degree = dwz63SharpDegree #marked N_X` the retention loss is `≍ 64 · (#marked / N_X) · Behrend`,
so `N_X` cancels and only `64 · Behrend(degree) ≤ lossHash N` is left --- and that is
subexponential in `N` because `Behrend d = exp (4 √(log (M d / 2)))` while `M d` is only
exponential in `N`.  Supplying that `lossHash` is bookkeeping over the client's own `degree`
sequence, and it is the only piece of `hrate` still open.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- **The hashing branch is strictly below `alphabar_X`.**  The only input is that the hash-loss
multiplier exceeds one; no enclosure of `exp dwz63EntropyX` is used. -/
theorem dwz63_hashingBranch_lt_exp : dwz63HashingBranch < Real.exp dwz63EntropyX := by
  unfold dwz63HashingBranch
  refine div_lt_self (Real.exp_pos _) ?_
  norm_num [dwz63HashLossMultiplier]

/-- **The hashing branch is attained by `N_X` itself, with no loss factor.**

This is the exponential half of the integration's `hrate`, in the form the six orientations
contribute: from some scale on, `dwz63HashingBranch ^ (6 (n+1)) ≤ N_X`.  Contrast
`dwz63_xRate_pow_le_dwz63XTypicalCount`, which is true but too weak here --- see the module
docstring. -/
theorem dwz63_hashingBranch_pow_le_dwz63XTypicalCount :
    ∃ cutoff : ℕ, ∀ t : ℕ, cutoff ≤ t → ∀ n : ℕ, n + 1 = 100000000 * t →
      dwz63HashingBranch ^ (6 * (n + 1)) ≤ ((dwz63XTypicalCount n t : ℕ) : ℝ) := by
  have hlower : (0 : ℝ) < dwz63HashingBranch ^ (100000000 : ℕ) :=
    pow_pos dwz63HashingBranch_pos _
  have hlt : dwz63HashingBranch ^ (100000000 : ℕ) <
      (2 : ℝ) ^ ((WordType.profileMass dwz63AlphaX : ℝ) *
        WordType.profileEntropyBits dwz63AlphaX) := by
    rw [WordType.two_rpow_mul_profileEntropyBits, profileMass_dwz63AlphaX,
      profileEntropyNats_dwz63AlphaX]
    rw [Real.exp_nat_mul]
    exact pow_lt_pow_left₀ dwz63_hashingBranch_lt_exp dwz63HashingBranch_pos.le (by norm_num)
  obtain ⟨cutoff, hcut⟩ := dwz63_exists_cutoff_pow_le_dwz63XTypicalCount hlower hlt
  refine ⟨cutoff, fun t ht n hn ↦ ?_⟩
  have h := hcut t ht n hn
  rwa [← pow_mul, show 100000000 * (6 * t) = 6 * (n + 1) by rw [hn]; ring] at h

/-- **The integration's `hrate`, reduced to the loss bookkeeping.**

Given the loss-free branch bound, `hrate` follows from the single inequality
`N_X * dwz63SharpRetentionLoss degree ≤ lossHash * #marked`, in which the marked count and the
sharp degree cancel against each other. -/
theorem dwz63_hrate_of_retentionLoss_le {n t degree : ℕ} {lossHash markedCard : ℝ}
    (hbranch : dwz63HashingBranch ^ (6 * (n + 1)) ≤ ((dwz63XTypicalCount n t : ℕ) : ℝ))
    (hloss : ((dwz63XTypicalCount n t : ℕ) : ℝ) * dwz63SharpRetentionLoss degree ≤
      lossHash * markedCard) :
    dwz63HashingBranch ^ (6 * (n + 1)) * dwz63SharpRetentionLoss degree ≤
      lossHash * markedCard := by
  refine le_trans (mul_le_mul_of_nonneg_right hbranch ?_) hloss
  exact le_of_lt (mul_pos (dwz63SharpModulusLoss_pos degree) (dwz63SharpBehrendLoss_pos degree))

end AlgebraicComplexity.Examples
