/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSupportBridge
import AlgebraicComplexity.MatrixMultiplication.SegmentedHoleRepair

/-!
# Section 6.3's segmentation data, and the segmented leaf

Layer 4 (`AlgebraicComplexity/Examples/`).  `MatrixMultiplication/SegmentedHoleRepair.lean` proves
the segmented Hole Lemma for an arbitrary segmentation.  This module supplies the
`[DuanWuZhou2022]` section 6.3 instance of that data and states the composition that turns a
segmented repair into the plain-power stage the campaign consumes.

## The fine partition and its `Z` alphabet

The coarse square is `((cwPartitionedTensor K q).positivePower 1).coarsen cwSquareDegreeMap`
(`CoppersmithWinogradSquare.lean:204`), and `cwSquareConstituent_eq_sum_sourceFiber` (`:219`)
expands each coarse constituent over the fibre of that coarsening.  So the *fine* partition
underneath a coarse cell is `(cwPartitionedTensor K q).positivePower 1`, whose block alphabet on
each leg is `PositiveWord CWBlock 1` --- an **ordered pair of base blocks**, which is
`[DuanWuZhou2022]`'s `(K̂_{2s-1}, K̂_{2s})` at `hole_lemma.tex:40` on the nose.  So a coarse word of
`n+1` letters has `n+1` fine letters, and the segmentation is `Fin (n+1) → Fin 15`.

A profile `Fin 15 → PositiveWord CWBlock 1 → ℕ` pins the **pair** distribution per segment, hence
the left-digit distribution `alphatilde_t`, with fifteen segments.  An intermediate convention
using the `CWBlock` alphabet and `2(n+1)` positions cannot do this ---
`Examples/DuanWuZhouLevelTwoFineProfiles.lean` proves it --- because there the two digits of a
coarse position land in different letters and a per-segment profile pools them.

## The segmentation depends on the word only through its type

`dwz63Seg` labels position `i` by the coarse cell of the letter at `i`, read through
`dwz63CellIndex` (`DuanWuZhouLevelTwoSupportBridge.lean:121`).  `card_fiber_dwz63Seg` records the
structural fact the paper note isolates: the size of segment `t` is the multiplicity of cell `t` in
the word, so two coarse words of the same type give segmentations that differ only by a permutation
of positions --- which is precisely what `Isomorphic.positiveSupportWordTensor_of_same_type`
(`WordTensorReindex.lean`) then absorbs.

## What is a parameter and why

`alphaTilde : Fin 15 → CWBlock → ℕ` --- the per-cell fine `Z` split --- is a
**parameter**, not a definition.  Its fifteen rows are `[DuanWuZhou2022]`'s `a` split on
`(0,2,2)`/`(2,0,2)`, `b` on `(1,1,2)`, `beta` on `(1,2,1)`/`(2,1,1)`, and the trivial split on the
plain matrix-multiplication cells; those numbers belong to the values lane's transcription table
and are not invented here.  Everything below is uniform in `alphaTilde`, so the table drops in
without any statement changing shape.

`hclaim3` is carried exactly as in `SegmentedHoleRepair.lean`: it is the only gated hypothesis.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u w

noncomputable section

/-! ## The fine partition -/

/-- **The fine partition underneath a coarse square cell**: the base Coppersmith--Winograd
partition itself.  Its `Z` alphabet is `CWBlock`, and the two fine letters sitting under one
coarse position are `[DuanWuZhou2022]`'s pair `(K̂_{2s-1}, K̂_{2s})`. -/
noncomputable def dwz63FinePartition (K : Type u) [CommRing K] :
    PartitionedTensor (K := K) (A := fun _ : Leg ↦ PositiveWord CWBlock 1)
      (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) :=
  (cwPartitionedTensor K dwz63Q).positivePower 1

/-! ## The segmentation induced by a coarse word -/

/-- **The segment labelling of section 6.3**: position `i` belongs to the segment of its coarse
cell. -/
def dwz63Seg (K : Type u) [CommRing K] (n : ℕ)
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :
    Fin (n + 1) → Fin 15 :=
  fun i ↦ dwz63CellIndex
    (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n w i).1

/-- **The segmentation depends on the word only through its type.**  Segment `t` has exactly as
many positions as the word has letters in cell `t`. -/
theorem card_fiber_dwz63Seg (K : Type u) [CommRing K] (n : ℕ)
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) (t : Fin 15) :
    (Finset.univ.filter fun i ↦ dwz63Seg K n w i = t).card =
      WordType.multiplicity (dwz63Seg K n w) t := by
  classical
  unfold WordType.multiplicity
  congr 2

/-! ## The segmented leaf -/

/-- **The candidate `𝒯*` of section 6.3**: the fine partition's power, cut segment by segment by
the per-cell fine `Z` split.  One leaf, one joint hole set --- not a product over cells. -/
noncomputable def dwz63SegmentedLeaf (K : Type u) [CommRing K] (n : ℕ)
    (seg : Fin (n + 1) → Fin 15)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ) :=
  (dwz63FinePartition K).segmentedRestrictedSplittingPower n 15 seg
    (SegmentedSplitRestriction.ofLeg Leg.Z alphaTilde)

/-- A broken copy of the segmented leaf, at one hole set. -/
noncomputable def dwz63BrokenSegmentedLeaf (K : Type u) [CommRing K] (n : ℕ)
    (seg : Fin (n + 1) → Fin 15)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (holes : Finset (SegmentedAvailableWord seg alphaTilde)) :=
  (dwz63SegmentedLeaf K n seg alphaTilde).holeSelect Leg.Z
    fun word ↦ word ∈ holes.image Subtype.val


end

end AlgebraicComplexity.Examples
