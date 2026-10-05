/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOnes

set_option autoImplicit false

/-!
# A zero-coordinate letter is determined by either live leg

Layer 4 (`AlgebraicComplexity/Examples/`).  The one-slice fusion
`CTensor.PermutedSharedOneSliceFiberData.restricts_permute_oneSliceMatrixMultiplication` takes
three support hypotheses: the shared leg carries one common label, and each of the two live legs
labels the fibre **injectively**.  This module proves the letterwise form of the injectivity, and
lifts it to words.

Among the six supported Coppersmith--Winograd base addresses, those with `.zero` on a fixed leg
are the three
`(0,2,0)`, `(0,0,2)`, `(0,1,1)` (up to the rotation naming that leg), whose labels on either live
leg are `last`, `zero`, `middle` --- pairwise distinct.  So a zero-coordinate letter is pinned by
its label on *either* live leg, which is the letterwise content of both `hx` and `hy`.  The three
cells with no zero coordinate allow no such reading; that is the same structural fact that makes
them the exceptional orbit.

The word-level lift is the expected one: a word is determined by its letters, the transposition
law reads each letter's label off the address, and the constant-zero hypothesis supplies the
zero-coordinate premise letterwise.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- **A supported zero-coordinate letter is determined by its first-live-leg label.**  A `decide`
over the six-address support and the three legs; both types are tiny. -/
theorem cwSupported_eq_of_zero_of_firstLiveLeg_eq (zero : Leg) :
    ∀ s ∈ cwBlockSupport, ∀ t ∈ cwBlockSupport,
      s zero = CWBlock.zero → t zero = CWBlock.zero →
        s (firstLiveLeg zero) = t (firstLiveLeg zero) → s = t := by
  cases zero <;> decide

/-- **A supported zero-coordinate letter is determined by its second-live-leg label.** -/
theorem cwSupported_eq_of_zero_of_secondLiveLeg_eq (zero : Leg) :
    ∀ s ∈ cwBlockSupport, ∀ t ∈ cwBlockSupport,
      s zero = CWBlock.zero → t zero = CWBlock.zero →
        s (secondLiveLeg zero) = t (secondLiveLeg zero) → s = t := by
  cases zero <;> decide

/-- **The word-level first-live-leg injectivity.**  Two supported words that are constantly zero on
the zero leg and agree on the first live leg are equal. -/
theorem positiveSupportWord_injective_of_zero_firstLiveLeg (zero : Leg) (m : ℕ)
    (w w' : PositiveWord cwBlockSupport m)
    (hw : positiveSupportWordBlockAddress cwBlockSupport m w zero =
      positiveWordConst .zero m)
    (hw' : positiveSupportWordBlockAddress cwBlockSupport m w' zero =
      positiveWordConst .zero m)
    (h : positiveSupportWordBlockAddress cwBlockSupport m w (firstLiveLeg zero) =
      positiveSupportWordBlockAddress cwBlockSupport m w' (firstLiveLeg zero)) :
    w = w' := by
  refine (positiveWordEquiv cwBlockSupport m).injective ?_
  funext position
  refine Subtype.ext ?_
  refine cwSupported_eq_of_zero_of_firstLiveLeg_eq zero _
    (positiveWordEquiv cwBlockSupport m w position).2 _
    (positiveWordEquiv cwBlockSupport m w' position).2
    (positiveSupportWord_letter_eq_zero_of_address_eq_const zero w hw position)
    (positiveSupportWord_letter_eq_zero_of_address_eq_const zero w' hw' position) ?_
  have hleft := congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive cwBlockSupport m w
      (firstLiveLeg zero)) position
  have hright := congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive cwBlockSupport m w'
      (firstLiveLeg zero)) position
  rw [← hleft, ← hright, h]

end AlgebraicComplexity.Examples
