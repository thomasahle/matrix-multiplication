/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarginalAmbient
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCopyCount

/-!
# `hselect` at the plain marginal-typical ambient

Layer 4 (`AlgebraicComplexity/Examples/`).  The plain analogue of
`Examples/DuanWuZhouLevelTwoMarginalAmbientSelect.lean`, joining the partition-level cut
`dwz63PlainMarginalKeep` to the word-level cut `Dwz63PlainMarginalTypical` and feeding the result
to the *parametric* `Tensor.Restricts.modeledTargets_to_markedXYIsolated`.

Every bridge it rides is generic and was verified unchanged for this setting:
`PartitionHashEncoding.positiveWordEquiv_supportWordAddress`
(`MatrixMultiplication/PartitionedPowerHashing.lean:72`),
`filter_modeledLegalTargets_eq_of_mem_iff` (`:570`), `positivePower_support_eq_modeledLegalTargets`
(`:550`) and `modeledTargets_to_markedXYIsolated`
(`MatrixMultiplication/MarkedXYPartitionedPowerHashing.lean:373`).

At the plain partition a leg label is a single coarse degree, so the transposition step needs no
phantom-argument pinning: the six-orientation version had to fix `DwzSymSixBlock Leg.X` against
`DwzSymSixBlock c` by hand, whereas here the block family is literally constant `Fin 5`.

## The X-side ceiling, restated

`card_image_x_dwz63PlainJointRetainedSupport` records that the retained family is *counted by* its
`X`-block words --- an equality, from the hash's own injectivity --- and
`dwz63_plainCopyCount_forces_card_xWords` propagates any copy count to that count.  Both are
stated on the retained family alone, so they are neutral with respect to where the `Z` cleanup is
placed.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## The two readings of the plain marginal cut agree -/

/-- **Transposing the word does not move the marginal condition.** -/
theorem dwz63PlainMarginalKeep_supportWordAddress (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) (c : Leg) :
    dwz63PlainMarginalKeep n t c (PartitionHashEncoding.supportWordAddress n q c) ↔
      WordType.multiplicity (fun j ↦ ((positiveWordEquiv _ n q j).val c)) =
        WordType.proportionalCounts (dwz63AlphaMarginal c) t := by
  have h : (positiveWordEquiv (Fin 5) n)
        (PartitionHashEncoding.supportWordAddress n q c) =
      fun j ↦ ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n) q j).val c :=
    PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ Fin 5) (support := (cwSquarePartitionedTensor K dwz63Q).support) n q c
  simp only [dwz63PlainMarginalKeep, h]

/-- **The word-level family is cut out by the legwise predicate.**  This is the `hkeep` premise of
`PartitionHashEncoding.filter_modeledLegalTargets_eq_of_mem_iff`. -/
theorem mem_dwz63PlainMarginalWords_iff_keep (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :
    q ∈ dwz63PlainMarginalWords K n t ↔
      ∀ c : Leg, dwz63PlainMarginalKeep n t c
        (PartitionHashEncoding.supportWordAddress n q c) := by
  rw [mem_dwz63PlainMarginalWords]
  constructor
  · intro h c
    exact (dwz63PlainMarginalKeep_supportWordAddress K n t q c).mpr (h c)
  · intro h c
    exact (dwz63PlainMarginalKeep_supportWordAddress K n t q c).mp (h c)

section Seam

variable {R : Type v} [Field R]

/-- **The seam.**  The marginal-typical subpartition's support is the modeled legal-target family
of the marginal-typical words. -/
theorem dwz63PlainMarginalTypicalPower_support (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ) :
    (dwz63PlainMarginalTypicalPower K n t).support =
      (cwSquarePartitionHashEncoding hinj).modeledAddresses n
        ((cwSquarePartitionHashEncoding hinj).legalTargets n
          (dwz63PlainMarginalWords K n t)) := by
  classical
  unfold dwz63PlainMarginalTypicalPower
  change ((cwSquarePartitionedTensor K dwz63Q).positivePower n).support.filter
      (fun s ↦ ∀ c, dwz63PlainMarginalKeep n t c (s c)) = _
  rw [(cwSquarePartitionHashEncoding hinj).positivePower_support_eq_modeledLegalTargets
    (cwSquarePartitionedTensor K dwz63Q) n]
  exact (cwSquarePartitionHashEncoding hinj).filter_modeledLegalTargets_eq_of_mem_iff
    n (dwz63PlainMarginalWords K n t) (dwz63PlainMarginalKeep n t)
    (mem_dwz63PlainMarginalWords_iff_keep K n t)

/-- **`hselect`, from the marginal-typical subpartition.** -/
theorem dwz63_restricts_plainMarginalTypicalPower_plainJointRetained [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts (dwz63PlainMarginalTypicalPower K n t).realize
      ((dwz63PlainMarginalTypicalPower K n t).withSupport
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)).realize :=
  Tensor.Restricts.modeledTargets_to_markedXYIsolated
    (cwSquarePartitionHashEncoding hinj) (dwz63PlainMarginalWords K n t) markedWords hmarked B hB
    seed (dwz63PlainMarginalTypicalPower K n t)
    (dwz63PlainMarginalTypicalPower_support K hinj n t)

/-- **`hselect` from the full plain positive power.**  The marginal cut composed with the hash. -/
theorem dwz63_restricts_positivePower_plainJointRetained [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts ((cwSquarePartitionedTensor K dwz63Q).positivePower n).realize
      ((dwz63PlainMarginalTypicalPower K n t).withSupport
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed)).realize :=
  (dwz63_restricts_positivePower_plainMarginalTypical K n t).trans
    (dwz63_restricts_plainMarginalTypicalPower_plainJointRetained K hinj n t markedWords hmarked
      B hB seed)

/-! ## The `X`-side ceiling at the plain partition -/

/-- **The retained family is counted by its `X`-block words**, an equality from the hash's own
injectivity, before any compatibility cleanup and independent of where one is placed. -/
theorem card_image_x_dwz63PlainJointRetainedSupport [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    ((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).image
        fun a ↦ a .X).card =
      (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card :=
  Finset.card_image_of_injOn
    (dwz63_x_injOn_plainJointRetained K hinj n t markedWords hmarked B hB seed)

/-- **Any copy count is a count of distinct `X`-block words.**  Stated at a free exponent, so it
applies both to the per-position count and to its sixth power. -/
theorem dwz63_plainCopyCount_forces_card_xWords [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) {loss : ℝ} {m : ℕ}
    (hcount : dwz63TrueCopyRate ^ m ≤
      loss * ((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card : ℝ)) :
    dwz63TrueCopyRate ^ m ≤
      loss * (((dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).image
        fun a ↦ a .X).card : ℝ) := by
  rw [card_image_x_dwz63PlainJointRetainedSupport K hinj n t markedWords hmarked B hB seed]
  exact hcount

end Seam

end AlgebraicComplexity.Examples
