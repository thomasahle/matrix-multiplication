/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOneSlice
import AlgebraicComplexity.MatrixMultiplication.PermutedCoherentOneSliceWord

set_option autoImplicit false

/-!
# Coherent one-slice word certificates in the rotated zero-`X` and zero-`Y` frames

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoFineCellOneSlice.lean`
supplies the *letterwise* coherent bases in the two rotated frames.  This module runs the committed
recursion `OneSliceRestriction.permutedCoherentWord`
(`MatrixMultiplication/PermutedCoherentOneSliceWord.lean`) on them, giving a coherent one-slice
certificate for an arbitrary supported **word** of base Coppersmith--Winograd blocks whose shared
leg is `X` (respectively `Y`).

The committed zero-`Z` instance of the same recursion is `cwZeroBaseWordCoherentRestriction`
(`Examples/CoppersmithWinogradZeroCoherentRestriction.lean`); nothing here re-proves it, and the
two rotated frames are obtained by supplying a different base to the same generic recursion.

## Why the pair case is the one `[DuanWuZhou2022]` needs

The fine alphabet of section 6.3 is `PositiveWord CWBlock 1` --- an ordered *pair* of level-one CW
blocks --- because the fine partition is `(cwPartitionedTensor K q).positivePower 1`.  A fine
letter is therefore a length-one word of base blocks, so `r = 1` below is exactly the fine-letter
certificate, and its matrix dimension `positiveWordProduct … 1 word` is the product of the two
level-one dimensions.  That product is the `q ^ ones s` that
`ZeroCoordinateMerge.mergedDimension` sums over the `alphatilde`-typical fibre.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## The zero-`X` frame -/

/-- The canonical shared-leg map of a word of zero-`X` base blocks: the iterated one-slice
coordinate product of `cwZeroXBaseCanonicalZMap` with itself. -/
noncomputable def cwZeroXWordCanonicalZMap (r : ℕ) :
    PositivePowerBlockSpace K (CWPartitionBlockSpace K q) r .X
        (positiveWordConst CWBlock.zero r) →ₗ[K] MMSpace K 1 1 1 .Z :=
  OneSliceRestriction.constWordZMap (V := CWPartitionBlockSpace K q) .X
    (cwZeroXBaseCanonicalZMap K q) r

/-- **Coherent one-slice data for a supported word in the zero-`X` fibre.**  The rotated-frame
analogue of the committed `cwZeroBaseWordCoherentRestriction`, obtained by running the same
recursion on `cwZeroXBaseCoherentRestriction`. -/
noncomputable def cwZeroXWordCoherentRestriction (r : ℕ)
    (word : PositiveWord cwBlockSupport r)
    (hz : positiveSupportWordBlockAddress cwBlockSupport r word .X =
      positiveWordConst CWBlock.zero r) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation .X)
          ((cwPartitionedTensor K q).positiveSupportWordTensor r word))
        (positiveWordProduct
          (fun s ↦ cwBaseConstituentDimension q s (secondLiveLeg .X)) r word) //
      HEq (C.legMap .Z) (cwZeroXWordCanonicalZMap K q r) } :=
  OneSliceRestriction.permutedCoherentWord (cwPartitionedTensor K q)
    (fun s ↦ cwBaseConstituentDimension q s (secondLiveLeg .X))
    (zeroOrientation .X) (cwZeroXBaseCanonicalZMap K q)
    (fun support hzero ↦ cwZeroXBaseCoherentRestriction K q support hzero) r word hz

/-- **The zero-`X` fine-letter certificate**, the `r = 1` instance: a fine letter of
`[DuanWuZhou2022]` section 6.3 is an ordered pair of level-one blocks. -/
noncomputable def cwZeroXPairCoherentRestriction
    (word : PositiveWord cwBlockSupport 1)
    (hz : positiveSupportWordBlockAddress cwBlockSupport 1 word .X =
      positiveWordConst CWBlock.zero 1) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation .X)
          ((cwPartitionedTensor K q).positiveSupportWordTensor 1 word))
        (positiveWordProduct
          (fun s ↦ cwBaseConstituentDimension q s (secondLiveLeg .X)) 1 word) //
      HEq (C.legMap .Z) (cwZeroXWordCanonicalZMap K q 1) } :=
  cwZeroXWordCoherentRestriction K q 1 word hz

/-! ## The zero-`Y` frame -/

/-- The canonical shared-leg map of a word of zero-`Y` base blocks. -/
noncomputable def cwZeroYWordCanonicalZMap (r : ℕ) :
    PositivePowerBlockSpace K (CWPartitionBlockSpace K q) r .Y
        (positiveWordConst CWBlock.zero r) →ₗ[K] MMSpace K 1 1 1 .Z :=
  OneSliceRestriction.constWordZMap (V := CWPartitionBlockSpace K q) .Y
    (cwZeroYBaseCanonicalZMap K q) r

/-- **Coherent one-slice data for a supported word in the zero-`Y` fibre.** -/
noncomputable def cwZeroYWordCoherentRestriction (r : ℕ)
    (word : PositiveWord cwBlockSupport r)
    (hz : positiveSupportWordBlockAddress cwBlockSupport r word .Y =
      positiveWordConst CWBlock.zero r) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation .Y)
          ((cwPartitionedTensor K q).positiveSupportWordTensor r word))
        (positiveWordProduct
          (fun s ↦ cwBaseConstituentDimension q s (secondLiveLeg .Y)) r word) //
      HEq (C.legMap .Z) (cwZeroYWordCanonicalZMap K q r) } :=
  OneSliceRestriction.permutedCoherentWord (cwPartitionedTensor K q)
    (fun s ↦ cwBaseConstituentDimension q s (secondLiveLeg .Y))
    (zeroOrientation .Y) (cwZeroYBaseCanonicalZMap K q)
    (fun support hzero ↦ cwZeroYBaseCoherentRestriction K q support hzero) r word hz

end AlgebraicComplexity.Examples
