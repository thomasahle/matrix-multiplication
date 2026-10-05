/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellUniform

set_option autoImplicit false

/-!
# On a zero-coordinate word the two live legs carry the same middle count

Layer 4 (`AlgebraicComplexity/Examples/`).  The remaining `huniform` obligation, for the
`(0,2,2)`-type cells, is that `dwz63CellOnes` --- a count on the **first** live leg --- is pinned by
`alphatilde`, which constrains the **second** live leg (`ofLeg Leg.Z`).  The bridge is an exact
symmetry, and it is elementary: a supported Coppersmith--Winograd letter has its three degrees
summing to `2`, so once the zero leg carries degree `0` the other two degrees sum to `2`, and one of
them is `1` exactly when the other is.  Middle digits on the two live legs therefore occur at
exactly the same positions.

`cwSupported_middleIndicator_liveLegs_eq` is that letterwise fact (a `decide` over the six-address
support and the three legs, both tiny), and `dwz63_middleCount_liveLegs_eq` is its word form: the
two live legs of a zero-coordinate supported word have equal middle counts, at any length.

With it, the `alphatilde`-pinned uniformity reduces to a statement purely about the constrained
leg, with no transport between legs left to do.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

/-- **Letterwise: on a zero-coordinate supported letter the two live legs are middle together.**
The three degrees sum to `2`, so with the zero leg at degree `0` the two live degrees sum to `2`,
and one is `1` exactly when the other is. -/
theorem cwSupported_middleIndicator_liveLegs_eq (zero : Leg) :
    ∀ s ∈ cwBlockSupport, s zero = CWBlock.zero →
      ((cwBlockDigit (s (firstLiveLeg zero)) = (1 : SplitDigit)) ↔
        (cwBlockDigit (s (secondLiveLeg zero)) = (1 : SplitDigit))) := by
  cases zero <;> decide

/-- **Word form: the two live legs of a zero-coordinate supported word carry the same middle
count.**  Both sides are sums of the same indicators, position by position. -/
theorem dwz63_middleCount_liveLegs_eq (zero : Leg) (n : ℕ)
    (w : PositiveWord cwBlockSupport n)
    (hz : positiveSupportWordBlockAddress cwBlockSupport n w zero =
      positiveWordConst .zero n) :
    cwWordMiddleCount n
        (positiveSupportWordBlockAddress cwBlockSupport n w (firstLiveLeg zero)) =
      cwWordMiddleCount n
        (positiveSupportWordBlockAddress cwBlockSupport n w (secondLiveLeg zero)) := by
  unfold cwWordMiddleCount
  refine Finset.sum_congr rfl ?_
  intro position _
  have hfirst := congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive cwBlockSupport n w
      (firstLiveLeg zero)) position
  have hsecond := congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive cwBlockSupport n w
      (secondLiveLeg zero)) position
  rw [hfirst, hsecond]
  have hzero := positiveSupportWord_letter_eq_zero_of_address_eq_const zero w hz position
  have hiff := cwSupported_middleIndicator_liveLegs_eq zero
    (positiveWordEquiv cwBlockSupport n w position).1
    (positiveWordEquiv cwBlockSupport n w position).2 hzero
  by_cases hcase : cwBlockDigit
      ((positiveWordEquiv cwBlockSupport n w position).1 (firstLiveLeg zero)) = (1 : SplitDigit)
  · rw [if_pos hcase, if_pos (hiff.mp hcase)]
  · rw [if_neg hcase, if_neg (fun h ↦ hcase (hiff.mpr h))]

end AlgebraicComplexity.Examples
