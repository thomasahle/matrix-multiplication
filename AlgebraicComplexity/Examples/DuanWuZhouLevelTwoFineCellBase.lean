/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellWord
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOnes

set_option autoImplicit false

/-!
# The fine-letter coherent base, at a transparent dimension

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` section 6.3's fine partition is
`(cwPartitionedTensor K q).positivePower 1`, whose block labels are ordered *pairs* of level-one
CW blocks.  The cell word of the reference leaf is a word over **that** partition, so the
recursion `OneSliceRestriction.permutedCoherentWord` has to be run a second time with the fine
partition as its base --- and its `base` argument is indexed by fine *block addresses*, not by
decoded level-one words.

`Examples/DuanWuZhouLevelTwoFineCellWord.lean` supplies the certificate for a decoded word, at
dimension `positiveWordProduct …`.  Passing that dimension up would reintroduce a choice-based
decode inside a definition, which is exactly what
`Examples/DuanWuZhouLevelTwoFineCellOnes.lean` exists to avoid.  So the dimension carried here is
the transparent `dwz63FineDimension = q ^ dwz63FineOnes`, read off the block address alone, and
the decode appears only inside the *proof*, where its opacity costs nothing.

`dwz63FineOnes` counts the middle level-one digits on the first live leg of a fine letter.  Because
the fine letter is a length-one word, that is a count over two digits, and it is the exponent whose
sum over the cell word `ZeroCoordinateMerge.mergedDimension` totals.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- **The one-slice exponent of a fine letter**, read off its block address: the number of middle
level-one digits on the first live leg of the zero-coordinate frame. -/
def dwz63FineOnes (zero : Leg)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1)) : ℕ :=
  cwWordMiddleCount 1 (s (firstLiveLeg zero))

/-- **The one-slice dimension of a fine letter**, transparently a power of `q`. -/
def dwz63FineDimension (q : ℕ) (zero : Leg)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1)) : ℕ :=
  q ^ dwz63FineOnes zero s

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **The zero-`X` fine-letter coherent base.**  A supported fine letter whose `X` pair is the
constant zero pair, with its one-slice certificate at the transparent dimension and the retained
shared-leg coherence. -/
noncomputable def dwz63FineZeroXBase
    (s : ((cwPartitionedTensor K q).positivePower 1).support)
    (hz : s.1 .X = positiveWordConst CWBlock.zero 1) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation .X)
          (((cwPartitionedTensor K q).positivePower 1).constituent s.1))
        (dwz63FineDimension q .X s.1) //
      HEq (C.legMap .Z) (cwZeroXWordCanonicalZMap K q 1) } := by
  classical
  obtain ⟨a, ha⟩ := s
  refine Classical.choice ?_
  obtain ⟨word, hword⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support 1 ha
  subst hword
  refine ⟨?_⟩
  have hzWord : positiveSupportWordBlockAddress cwBlockSupport 1 word .X =
      positiveWordConst CWBlock.zero 1 := hz
  have hdim : dwz63FineDimension q .X
        (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support 1 word) =
      positiveWordProduct
        (fun t ↦ cwBaseConstituentDimension q t (secondLiveLeg .X)) 1 word :=
    (positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_cwWordMiddleCount q .X 1 word
      hzWord).symm
  rw [(cwPartitionedTensor K q).positivePower_constituent_positiveSupportWordBlockAddress 1 word,
    hdim]
  exact cwZeroXPairCoherentRestriction K q word hzWord

/-- **The zero-`Y` fine-letter coherent base.** -/
noncomputable def dwz63FineZeroYBase
    (s : ((cwPartitionedTensor K q).positivePower 1).support)
    (hz : s.1 .Y = positiveWordConst CWBlock.zero 1) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation .Y)
          (((cwPartitionedTensor K q).positivePower 1).constituent s.1))
        (dwz63FineDimension q .Y s.1) //
      HEq (C.legMap .Z) (cwZeroYWordCanonicalZMap K q 1) } := by
  classical
  obtain ⟨a, ha⟩ := s
  refine Classical.choice ?_
  obtain ⟨word, hword⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support 1 ha
  subst hword
  refine ⟨?_⟩
  have hzWord : positiveSupportWordBlockAddress cwBlockSupport 1 word .Y =
      positiveWordConst CWBlock.zero 1 := hz
  have hdim : dwz63FineDimension q .Y
        (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support 1 word) =
      positiveWordProduct
        (fun t ↦ cwBaseConstituentDimension q t (secondLiveLeg .Y)) 1 word :=
    (positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_cwWordMiddleCount q .Y 1 word
      hzWord).symm
  rw [(cwPartitionedTensor K q).positivePower_constituent_positiveSupportWordBlockAddress 1 word,
    hdim]
  exact cwZeroYWordCoherentRestriction K q 1 word hzWord

end AlgebraicComplexity.Examples
