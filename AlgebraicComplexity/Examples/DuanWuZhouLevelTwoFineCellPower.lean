/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellBase

set_option autoImplicit false

/-!
# The cell word: the second run of the coherent one-slice recursion

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` section 6.3's reference leaf is a
word of `m + 1` **fine** letters over the partition `(cwPartitionedTensor K q).positivePower 1`.
`Examples/DuanWuZhouLevelTwoFineCellBase.lean` supplies the coherent certificate of one such
letter, indexed by its block address and carrying the transparent dimension
`dwz63FineDimension = q ^ dwz63FineOnes`.  Running `OneSliceRestriction.permutedCoherentWord` on
that base is the second of the two passes the committed chain performs --- "at the base letter and
at the chunk letter", in the words of `MatrixMultiplication/PermutedCoherentOneSliceWord.lean`.

## The exponent of a cell word

`dwz63CellOnes` totals `dwz63FineOnes` over the positions of a cell word, again reading only the
block address: it is the number of middle level-one digits on the first live leg across the whole
word.  `positiveWordProduct_dwz63FineDimension_eq_pow_dwz63CellOnes` is the resulting dimension
law, and it is stated for an arbitrary zero leg, so all three orientations are covered at once.
Its right-hand side `q ^ dwz63CellOnes …` is exactly the summand
`ZeroCoordinateMerge.mergedDimension q ones` totals over an `alphatilde`-typical fibre, with the
exponent constant on that fibre because the split profile pins the fine-letter multiplicities.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-- **The one-slice exponent of a whole cell word**, read off its block address: the middle
level-one digits on the first live leg, totalled over the word's positions. -/
def dwz63CellOnes (zero : Leg) (m : ℕ)
    (S : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) m)) : ℕ :=
  ∑ position,
    cwWordMiddleCount 1
      (positiveWordEquiv (PositiveWord CWBlock 1) m (S (firstLiveLeg zero)) position)

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **The cell-word dimension law**, in the transparent `q ^ ones` form the merge consumes.
Stated for an arbitrary zero leg. -/
theorem positiveWordProduct_dwz63FineDimension_eq_pow_dwz63CellOnes
    (zero : Leg) (m : ℕ)
    (word : PositiveWord ((cwPartitionedTensor K q).positivePower 1).support m) :
    positiveWordProduct
        (fun s ↦ dwz63FineDimension q zero s.1) m word =
      q ^ dwz63CellOnes zero m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m word) := by
  rw [positiveWordProduct_eq_fin_prod]
  unfold dwz63CellOnes
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl ?_
  intro position _
  unfold dwz63FineDimension dwz63FineOnes
  refine congrArg (fun w ↦ q ^ cwWordMiddleCount 1 w) ?_
  exact (congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      ((cwPartitionedTensor K q).positivePower 1).support m word (firstLiveLeg zero))
    position).symm

/-! ## The two rotated cell-word certificates -/

/-- **The zero-`X` cell-word coherent certificate.**  The second pass of the committed recursion,
run on the fine-letter base. -/
noncomputable def dwz63CellWordZeroXCoherent (m : ℕ)
    (word : PositiveWord ((cwPartitionedTensor K q).positivePower 1).support m)
    (hzero : positiveSupportWordBlockAddress
        ((cwPartitionedTensor K q).positivePower 1).support m word
        ((zeroOrientation .X).symm .Z) =
      positiveWordConst (positiveWordConst CWBlock.zero 1) m) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation .X)
          (((cwPartitionedTensor K q).positivePower 1).positiveSupportWordTensor m word))
        (positiveWordProduct (fun s ↦ dwz63FineDimension q .X s.1) m word) //
      HEq (C.legMap .Z)
        (OneSliceRestriction.constWordZMap
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q) 1)
          ((zeroOrientation .X).symm .Z) (cwZeroXWordCanonicalZMap K q 1) m) } :=
  OneSliceRestriction.permutedCoherentWord ((cwPartitionedTensor K q).positivePower 1)
    (fun s ↦ dwz63FineDimension q .X s.1) (zeroOrientation .X)
    (cwZeroXWordCanonicalZMap K q 1)
    (fun s hs ↦ dwz63FineZeroXBase K q s hs) m word hzero

/-- **The zero-`Y` cell-word coherent certificate.** -/
noncomputable def dwz63CellWordZeroYCoherent (m : ℕ)
    (word : PositiveWord ((cwPartitionedTensor K q).positivePower 1).support m)
    (hzero : positiveSupportWordBlockAddress
        ((cwPartitionedTensor K q).positivePower 1).support m word
        ((zeroOrientation .Y).symm .Z) =
      positiveWordConst (positiveWordConst CWBlock.zero 1) m) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation .Y)
          (((cwPartitionedTensor K q).positivePower 1).positiveSupportWordTensor m word))
        (positiveWordProduct (fun s ↦ dwz63FineDimension q .Y s.1) m word) //
      HEq (C.legMap .Z)
        (OneSliceRestriction.constWordZMap
          (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q) 1)
          ((zeroOrientation .Y).symm .Z) (cwZeroYWordCanonicalZMap K q 1) m) } :=
  OneSliceRestriction.permutedCoherentWord ((cwPartitionedTensor K q).positivePower 1)
    (fun s ↦ dwz63FineDimension q .Y s.1) (zeroOrientation .Y)
    (cwZeroYWordCanonicalZMap K q 1)
    (fun s hs ↦ dwz63FineZeroYBase K q s hs) m word hzero

end AlgebraicComplexity.Examples
