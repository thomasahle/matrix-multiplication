/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentedFineLeaf
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentationData
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineConfigurationWitness
import AlgebraicComplexity.MatrixMultiplication.SegmentedFiberUniformity

set_option autoImplicit false

/-!
# One common leaf for section 6.3, and what the segmentation remembers

Two facts about `dwz63Seg`, both consequences of the committed
`dwz63CellEquiv : Fin 15 ≃ CWSquareSupport`.

**The segmentation remembers the coarse word.**  `dwz63Seg` reads the fifteen-cell index off each
coarse letter, and on the coarsened square support that index is a *bijection*, not a lossy
label.  So `dwz63Seg` is injective (`dwz63Seg_injective`): a permutation of sample positions
preserves the segmentation exactly when it fixes the coarse word
(`dwz63_segPreserving_iff_fixes_word`).  This is the reason the segmented shuffling group of
`hole_lemma.tex` Claim 2 acts on a *single* localized fine fiber rather than moving between
fibers --- the shuffles available to the Hole Lemma are precisely the stabilizer of the retained
coarse word, and nothing is lost by localizing.

**One common leaf.**  For an arbitrary permutation the fiber does move, and it moves
isomorphically (`dwz63_segmentedFineFiber_isomorphic_position`): coarse words of the same type
have isomorphic segmented fine fibers.  Since all retained coarse words in
`dwz63PlainMarginalTypicalPower K n t` share the type `t`, every retained constituent's leaf is
isomorphic to one reference leaf.  That is the single leaf the batched Hole Lemma requires.

`[DuanWuZhou2022]`, `hole_lemma.tex`, `global_value.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The fifteen-cell index is injective on the coarsened square support -/

/-- On the coarsened square support the fifteen-cell index has a left inverse, so distinct
supported coarse letters have distinct cell indices. -/
theorem dwz63CellIndex_injOn_support (K : Type u) [CommRing K]
    (s t : ((cwSquarePartitionedTensor K dwz63Q).support : Finset CWSquareAddress))
    (h : dwz63CellIndex s.1 = dwz63CellIndex t.1) : s = t := by
  have hsupp : ∀ x : CWSquareAddress,
      x ∈ (cwSquarePartitionedTensor K dwz63Q).support ↔ x ∈ cwSquareSupport := by
    intro x
    rw [cwSquarePartitionedTensor_support]
  have hs : (s.1 : CWSquareAddress) ∈ cwSquareSupport := (hsupp _).1 s.2
  have ht : (t.1 : CWSquareAddress) ∈ cwSquareSupport := (hsupp _).1 t.2
  apply Subtype.ext
  rw [← dwz63Cell_dwz63CellIndex hs, ← dwz63Cell_dwz63CellIndex ht, h]

/-- **The segmentation remembers the coarse word.** -/
theorem dwz63Seg_injective (K : Type u) [CommRing K] (n : ℕ) :
    Function.Injective (dwz63Seg K n) := by
  intro w w' h
  apply (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).injective
  funext i
  exact dwz63CellIndex_injOn_support K _ _ (congrFun h i)

/-- Relabeling sample positions relabels the segmentation by the same permutation. -/
theorem dwz63Seg_positionEquiv (K : Type u) [CommRing K] (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :
    dwz63Seg K n
        (positiveWordPositionEquiv
          ((cwSquarePartitionedTensor K dwz63Q).support) n σ w) =
      dwz63Seg K n w ∘ ⇑σ := by
  funext i
  unfold dwz63Seg
  rw [positiveWordEquiv_position_apply]
  rfl

/-- **The segment-preserving shuffles are exactly the stabilizer of the retained coarse word.**

`hole_lemma.tex` Claim 2 shuffles by permutations that preserve the segmentation.  Here that is
the same condition as fixing the coarse word, so the shuffles act on the single localized fine
fiber over that word. -/
theorem dwz63_segPreserving_iff_fixes_word (K : Type u) [CommRing K] (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :
    (∀ i, dwz63Seg K n w (σ i) = dwz63Seg K n w i) ↔
      positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n σ w = w := by
  constructor
  · intro h
    apply dwz63Seg_injective K n
    rw [dwz63Seg_positionEquiv]
    funext i
    exact h i
  · intro h i
    have hseg := congrArg (dwz63Seg K n) h
    rw [dwz63Seg_positionEquiv] at hseg
    exact congrFun hseg i

/-- The localized coarse target is fixed by every segment-preserving shuffle. -/
theorem dwz63_positionRelabel_target_eq (K : Type u) [CommRing K] (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hperm : ∀ i, dwz63Seg K n w (σ i) = dwz63Seg K n w i) :
    positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5) n σ
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) n w) =
      positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) n w := by
  rw [positionRelabelBlockAddress_positiveSupportWordBlockAddress,
    (dwz63_segPreserving_iff_fixes_word K n σ w).1 hperm]

/-! ## One common leaf -/

/-- **Coarse words of the same type have isomorphic segmented fine fibers.**

The permutation moves the coarse target and the segmentation together, and
`segmentedLocalizedFiber_isomorphic_position` transports the localized selection along it.  Every
retained coarse word of a fixed type is a position relabeling of any other, so all their leaves
are isomorphic to one. -/
theorem dwz63_segmentedFineFiber_isomorphic_position (K : Type u) [CommRing K] (n : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (σ : Equiv.Perm (Fin (n + 1))) :
    Isomorphic
      (dwz63SegmentedFineFiber K n 15 (dwz63Seg K n w) alphaTilde
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) n w)).realize
      (dwz63SegmentedFineFiber K n 15
        (dwz63Seg K n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n σ w))
        alphaTilde
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n σ w))).realize := by
  rw [← dwz63SegmentedFineFiber_eq_fiberSelect, ← dwz63SegmentedFineFiber_eq_fiberSelect,
    dwz63Seg_positionEquiv K n σ w,
    ← positionRelabelBlockAddress_positiveSupportWordBlockAddress]
  exact segmentedLocalizedFiber_isomorphic_position
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n 15
    (dwz63Seg K n w)
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n w) σ

end AlgebraicComplexity.Examples
