/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationOneSlice

set_option autoImplicit false

/-!
# The one-slice exponent of a zero-coordinate cell, read off the block address

Layer 4 (`AlgebraicComplexity/Examples/`).  `ZeroCoordinateMerge.mergedDimension q ones cls`
sums `q ^ ones s` over a class of **block addresses**, so a client of the one-slice fusion must
present the exponent as a function

`ones : BlockAddress A → ℕ`,

not as a function of a decoded supported word.  The committed statistic
`cwSupportedWordMiddleCount` (`Examples/CoppersmithWinogradZeroOrientationOneSlice.lean:93`) is of
the latter shape: it counts middle letters of a `PositiveWord cwBlockSupport r`.  Reading it off a
word costs a decode through `exists_positiveSupportWord_of_mem_positivePower_support`, and a
choice-based decode inside a *definition* would make `ones` opaque -- precisely the failure mode
that `cwZeroBaseRotatedOneSliceRestriction`'s docstring records for `legMap`.

This module removes the decode.  `cwWordMiddleCount` counts middle digits of a plain
`PositiveWord CWBlock r`, which is exactly one leg of a block address, and
`cwSupportedWordMiddleCount_eq_cwWordMiddleCount` identifies the two.  The committed dimension law
then reads

`positiveWordProduct (cwBaseConstituentDimension q · (secondLiveLeg zero)) r word
    = q ^ cwWordMiddleCount r (address (firstLiveLeg zero))`,

whose right-hand side mentions only the block address.  That is the transparent `q ^ ones s` the
merge needs, and it is what makes `huniform` provable on an `alphatilde`-typical fibre: the split
profile pins the multiplicities of the fine letters, hence pins this count.

## Why a zero coordinate is what makes this work

Over a cell with a zero coordinate the supported level-one letters are confined to three
addresses, and each is determined by its label on a single live leg; the committed
`cwBaseConstituentDimension_secondLiveLeg_eq_pow_middleIndicator_of_eq_zero` is that
characterisation in dimension form.  The three cells with no zero coordinate --- `(1,1,2)`,
`(1,2,1)`, `(2,1,1)` --- allow no such reading, which is the same structural reason they are not
matrix-multiplication tensors.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `lem:non-rot-values`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- **Middle-digit count of a plain block word.**  One leg of a block address is a
`PositiveWord CWBlock r`; this counts its middle letters, with no reference to a supported word. -/
def cwWordMiddleCount (r : ℕ) (w : PositiveWord CWBlock r) : ℕ :=
  ∑ position,
    if cwBlockDigit (positiveWordEquiv CWBlock r w position) = (1 : SplitDigit) then 1 else 0

/-- **The committed word statistic is a function of the block address.**  Both sides count middle
letters at the same positions; the recursive transposition law identifies the letters. -/
theorem cwSupportedWordMiddleCount_eq_cwWordMiddleCount (c : Leg) (r : ℕ)
    (word : PositiveWord cwBlockSupport r) :
    cwSupportedWordMiddleCount c r word =
      cwWordMiddleCount r (positiveSupportWordBlockAddress cwBlockSupport r word c) := by
  unfold cwSupportedWordMiddleCount cwWordMiddleCount
  refine Finset.sum_congr rfl ?_
  intro position _
  refine congrArg (fun b ↦ if cwBlockDigit b = (1 : SplitDigit) then 1 else 0) ?_
  exact (congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive cwBlockSupport r word c)
    position).symm

/-- **The one-slice exponent of a zero-coordinate word, read off the block address.**

The committed
`positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_middleCount_of_eq_const` with its
right-hand side rewritten through `cwSupportedWordMiddleCount_eq_cwWordMiddleCount`.  This is the
form `ZeroCoordinateMerge.mergedDimension` consumes. -/
theorem positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_cwWordMiddleCount
    (q : ℕ) (zero : Leg) (r : ℕ) (word : PositiveWord cwBlockSupport r)
    (hzero : positiveSupportWordBlockAddress cwBlockSupport r word zero =
      positiveWordConst .zero r) :
    positiveWordProduct
        (fun support ↦ cwBaseConstituentDimension q support (secondLiveLeg zero)) r word =
      q ^ cwWordMiddleCount r
        (positiveSupportWordBlockAddress cwBlockSupport r word (firstLiveLeg zero)) := by
  rw [positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_middleCount_of_eq_const q zero r
      word hzero,
    cwSupportedWordMiddleCount_eq_cwWordMiddleCount (firstLiveLeg zero) r word]

end AlgebraicComplexity.Examples
