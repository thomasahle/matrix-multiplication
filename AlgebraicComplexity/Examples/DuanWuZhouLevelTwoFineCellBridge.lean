/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellResum

set_option autoImplicit false

/-!
# The exponent, read on the leg `alphatilde` actually constrains

Layer 4 (`AlgebraicComplexity/Examples/`).  `dwz63CellOnes` counts middle digits on the **first**
live leg, while `[DuanWuZhou2022]` section 6.3's split profile is `ofLeg Leg.Z`, constraining the
**second**.  This module removes that mismatch, and with it the last obstruction to `huniform` for
the split-restricted cells.

The transfer needs no multiplicity bookkeeping: `Examples/DuanWuZhouLevelTwoFineCellLiveLegs.lean`
already equates the two live legs' middle counts on any zero-coordinate supported word, so applying
it at `n = 1` --- a fine letter *is* a length-one word of base blocks --- gives the equality
position by position, and summing transports `dwz63CellOnes` onto the constrained leg outright.
`Examples/DuanWuZhouLevelTwoFineCellResum.lean` then reads it off the empirical type.

Composing the two, the exponent of a cell word is the `alphatilde`-weighted total
`∑_p alphatilde p * cwWordMiddleCount 1 p`: constant on the fibre, and explicitly computable from
the profile row.  For `(0,2,2)` only the pair `(1,1)` carries a nonzero middle count, namely `2`,
so the total is `2 * alphatilde (1,1)` --- the `2(1-2a)(m+1)` of the paper's `q^{2(1-2a)m}`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **A fine letter has the same middle count on both live legs.**  Image 81's word statement at
`n = 1`, transported through the decode of a supported fine address. -/
theorem dwz63_fineLetter_middleCount_liveLegs_eq (zero : Leg)
    (s : ((cwPartitionedTensor K q).positivePower 1).support)
    (hz : s.1 zero = positiveWordConst CWBlock.zero 1) :
    cwWordMiddleCount 1 (s.1 (firstLiveLeg zero)) =
      cwWordMiddleCount 1 (s.1 (secondLiveLeg zero)) := by
  obtain ⟨w, hw⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support 1 s.2
  rw [show s.1 (firstLiveLeg zero) =
      positiveSupportWordBlockAddress cwBlockSupport 1 w (firstLiveLeg zero) from
    (congrFun hw (firstLiveLeg zero)).symm,
    show s.1 (secondLiveLeg zero) =
      positiveSupportWordBlockAddress cwBlockSupport 1 w (secondLiveLeg zero) from
    (congrFun hw (secondLiveLeg zero)).symm]
  refine dwz63_middleCount_liveLegs_eq zero 1 w ?_
  rw [show positiveSupportWordBlockAddress cwBlockSupport 1 w zero = s.1 zero from
    congrFun hw zero]
  exact hz

/-- **The cell exponent, read on the constrained leg.**  Summing the letterwise equality moves
`dwz63CellOnes` from the first live leg onto the second, which is the one `alphatilde` pins. -/
theorem dwz63_cellOnes_eq_sum_secondLive (zero : Leg) (m : ℕ)
    (w : PositiveWord ((cwPartitionedTensor K q).positivePower 1).support m)
    (hzero : ∀ position,
      (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support m w position).1
        zero = positiveWordConst CWBlock.zero 1) :
    dwz63CellOnes zero m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m w) =
      ∑ position,
        cwWordMiddleCount 1
          (positiveWordEquiv (PositiveWord CWBlock 1) m
            (positiveSupportWordBlockAddress
              ((cwPartitionedTensor K q).positivePower 1).support m w (secondLiveLeg zero))
            position) := by
  unfold dwz63CellOnes
  refine Finset.sum_congr rfl ?_
  intro position _
  rw [show positiveWordEquiv (PositiveWord CWBlock 1) m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m w (firstLiveLeg zero))
        position =
      (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support m w position).1
        (firstLiveLeg zero) from
    congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
        ((cwPartitionedTensor K q).positivePower 1).support m w (firstLiveLeg zero)) position,
    show positiveWordEquiv (PositiveWord CWBlock 1) m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m w (secondLiveLeg zero))
        position =
      (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support m w position).1
        (secondLiveLeg zero) from
    congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
        ((cwPartitionedTensor K q).positivePower 1).support m w (secondLiveLeg zero)) position]
  exact dwz63_fineLetter_middleCount_liveLegs_eq K q zero
    (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support m w position)
    (hzero position)

/-- **`huniform` for the split-restricted cells.**  The exponent is the `alphatilde`-weighted total
of the per-pair middle count, hence constant on the whole `alphatilde`-typical fibre. -/
theorem dwz63_cellOnes_eq_alphaTilde_sum (zero : Leg) (m : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (w : PositiveWord ((cwPartitionedTensor K q).positivePower 1).support m)
    (hzero : ∀ position,
      (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support m w position).1
        zero = positiveWordConst CWBlock.zero 1)
    (htype : WordType.multiplicity
      (positiveWordEquiv (PositiveWord CWBlock 1) m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m w (secondLiveLeg zero))) = α) :
    dwz63CellOnes zero m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m w) =
      ∑ p : PositiveWord CWBlock 1, α p * cwWordMiddleCount 1 p := by
  rw [dwz63_cellOnes_eq_sum_secondLive K q zero m w hzero,
    WordType.sum_word_eq_sum_multiplicity_mul (cwWordMiddleCount 1)
      (positiveWordEquiv (PositiveWord CWBlock 1) m
        (positiveSupportWordBlockAddress
          ((cwPartitionedTensor K q).positivePower 1).support m w (secondLiveLeg zero))),
    htype]

end AlgebraicComplexity.Examples
