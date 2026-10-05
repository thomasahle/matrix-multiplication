/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAggregateBatching

set_option autoImplicit false

/-!
# The batching loss is subexponential

The level-two endpoints carry a `batchLoss : ℕ → ℝ` together with `Growth.Subexponential
batchLoss`, and bound the retained support of a length-`n + 1` stage by
`batchLoss (n + 1) * (number of batches)`.  The batch size that discharges that bookkeeping is
`dwz63GoodBatchSize n = 5 * (n + 1) + 1` (`Examples/DuanWuZhouLevelTwoAggregateBatching.lean:42`),
the finite form of the divisor `N * l + 2` in `cor:hole_lemma`
(`papers/sources/2210.10173/hole_lemma.tex:159-168`), which turns `s` broken copies with non-hole
fractions `eta_1, ..., eta_s` into `floor ((sum eta_t) / (N * l + 2))` complete copies.

This module records that the loss the endpoint actually wants --- four batches' worth at the
*predecessor* length, `fun m => 4 * dwz63GoodBatchSize (m - 1)`, which is how the length index
`n + 1` of the stage meets the index `m` of the growth statement --- is subexponential.  The
content is only that the batch size is affine in the length: DWZ absorb it in the `n^{O(1)}`
slack that every rate comparison in section 6 tolerates, and `Growth.Subexponential` is that
tolerance made explicit.

The truncated subtraction is deliberate and harmless: at `m = 0` it reads `4 * dwz63GoodBatchSize
0 = 24`, which the affine majorant `20 * m + 24` still covers.

`[duan2023faster]`, `hole_lemma.tex:159-168`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

/-- The batching loss is bounded by an affine function of the index.

At `m = 0` truncated subtraction gives `4 * dwz63GoodBatchSize 0 = 24`, and at `m ≥ 1` the value
is `4 * (5 * m + 1) = 20 * m + 4`; both are at most `20 * m + 24`. -/
theorem dwz63_four_mul_goodBatchSize_pred_le (m : ℕ) :
    4 * dwz63GoodBatchSize (m - 1) ≤ 20 * m + 24 := by
  unfold dwz63GoodBatchSize
  omega

/-- **The batching loss is subexponential.**

An affine majorant suffices: `Growth.Subexponential.natCast_pow 1` supplies `fun m ↦ (m : ℝ)`,
`const_mul` and `add` scale and shift it, and `mono` transports the bound along
`dwz63_four_mul_goodBatchSize_pred_le`. -/
theorem dwz63_subexponential_four_mul_goodBatchSize_pred :
    Growth.Subexponential (fun m : ℕ ↦ ((4 * dwz63GoodBatchSize (m - 1) : ℕ) : ℝ)) := by
  refine Growth.Subexponential.mono
    (((Growth.Subexponential.natCast_pow 1).const_mul (by norm_num : (0 : ℝ) ≤ 20)).add
      (Growth.Subexponential.const (by norm_num : (0 : ℝ) ≤ 24)))
    (fun m ↦ Nat.cast_nonneg _) (fun m ↦ ?_)
  have hcast : ((4 * dwz63GoodBatchSize (m - 1) : ℕ) : ℝ) ≤ ((20 * m + 24 : ℕ) : ℝ) :=
    Nat.cast_le.2 (dwz63_four_mul_goodBatchSize_pred_le m)
  simp only [pow_one]
  push_cast at hcast ⊢
  linarith

end AlgebraicComplexity.Examples
