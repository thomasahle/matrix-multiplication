/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineExpansion
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedHoleRepair

set_option autoImplicit false

/-!
# The segmented fine leaf: `hleaf`, proved

Layer 4 (`AlgebraicComplexity/Examples/`).  Two corrections, both load-bearing, and then the
consequence.

## Correction 1 --- `select` *does* take word-level predicates

`Examples/DuanWuZhouLevelTwoFineExpansion.lean` flags as "the one genuinely remaining step" that
the committed bridges "select the fine family by a **legwise** predicate `keep : ∀ c, … → Prop`,
one fine label at a time", so that "a multiplicity constraint is not letterwise, and `select keep`
does not express it".  I stated the same thing, and it is wrong.  The predicate in its own
instantiation is

`keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop`,

which takes the **whole word** on each leg, not one label.  A per-segment multiplicity condition is
exactly of that form --- indeed
`PartitionedTensor.segmentedRestrictedSplittingPower P n m seg profile` is *defined* as
`(P.positivePower n).select (profile.Keeps n seg)`
(`MatrixMultiplication/SegmentedSplitRestriction.lean`).  So no new lemma is needed: the step is an
instantiation, and `dwz63_hleaf_segmentedFineFiber` below is it.

## Correction 2 --- the fine alphabet is the *pair*, so `Fin 15` suffices

The committed bridge produces a fine word over `PositiveWord CWBlock 1`: the fine partition is
`(cwPartitionedTensor K q).positivePower 1`, so one fine letter is an **ordered pair of base
blocks** --- `[DuanWuZhou2022]`'s `(K̂_{2s-1}, K̂_{2s})` at `hole_lemma.tex:40` on the nose --- and a
coarse word of `n+1` letters has `n+1` fine letters, not `2(n+1)`.

A profile `Fin 15 → PositiveWord CWBlock 1 → ℕ` therefore pins the **pair** distribution per
segment, hence the left-digit distribution `α̃_t`, with fifteen segments.  My
`pooled_segmentMultiplicity_does_not_determine_left_digit`
(`Examples/DuanWuZhouLevelTwoFineProfiles.lean`) remains true and remains a proof --- but it is a
proof about the `CWBlock` alphabet, where a fine letter is half a coarse position.  With the pair
alphabet the defect it exhibits does not arise, because the two digits sit in one letter.

So the parity refinement `Fin 30` is **not needed**: it repairs a defect introduced by moving to
the `CWBlock` alphabet.  The alphabet the committed machinery hands us is the one to keep.

## What this module proves

`hleaf` in the forward direction, at the segmented cut: a retained coarse-word constituent
restricts to its fine fiber cut segment by segment at `α̃`.  This is the premise
`dwz63_plainStage_of_segmentedRepair` takes as a hypothesis, now discharged.

## What remains

Two things, both named and neither gated by Claim 3:

* **Uniformity.**  `dwz63SegmentedFineFiber … target` depends on `target`; the batched Hole Lemma
  needs one common leaf.  Two targets of the same coarse type have isomorphic fibers, and
  `Isomorphic.positiveSupportWordTensor_of_same_type`
  (`MatrixMultiplication/WordTensorReindex.lean`) is the tool.
* **Breaking.**  The Hole Lemma consumes `holeSelect Leg.Z holes` of the leaf; composing that with
  the restriction below is one `Restricts.trans` once the hole supplier exists.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

/-- **The segmented fine leaf of one retained coarse block.**  The fine fiber over `target`, cut
segment by segment by the per-segment pair profile `alphaTilde`.  This is `[DuanWuZhou2022]`'s `T*`
for that block. -/
noncomputable def dwz63SegmentedFineFiber (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n)) :=
  ((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
    cwSquareDegreeMap n m seg
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde) target

/-- The leaf, in the fiber-then-select spelling `dwz63_coarseWord_restricts_fineFiberSelect`
produces.  `coarseningFiber_select_eq_segmentedLocalizedSplittingPower` is the whole content. -/
theorem dwz63SegmentedFineFiber_eq_fiberSelect (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n)) :
    ((((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) target).select
      ((SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n seg) =
      dwz63SegmentedFineFiber K n m seg alphaTilde target :=
  PartitionedTensor.coarseningFiber_select_eq_segmentedLocalizedSplittingPower
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n m seg
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde) target

/-- **`hleaf`, proved.**

A retained coarse-word constituent restricts to its fine fiber cut at the segmented split.  The
proof is `dwz63_coarseWord_restricts_fineFiberSelect` instantiated at the segmented keep predicate;
no new mathematics, because `select` accepts a whole-word predicate per leg and
`SegmentedSplitRestriction.Keeps` is one. -/
theorem dwz63_hleaf_segmentedFineFiber (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target ∈
      (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).support) :
    Restricts
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).constituent target)
      (dwz63SegmentedFineFiber K n m seg alphaTilde target).realize := by
  rw [← dwz63SegmentedFineFiber_eq_fiberSelect]
  exact dwz63_coarseWord_restricts_fineFiberSelect K n target htarget
    ((SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n seg)

/-- The indexed form: every retained copy expands to its own segmented fine leaf, outer index
untouched.  This is the left-hand side the batched Hole Lemma consumes. -/
theorem dwz63_indexedDirectSum_hleaf_segmentedFineFiber
    {I : Type*} [Fintype I] (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : I → BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : ∀ i, target i ∈
      (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
        cwSquareDegreeMap n).support) :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦
        (((cwPartitionedTensor K dwz63Q).positivePower 1).coarsenedPositivePower
          cwSquareDegreeMap n).constituent (target i)))
      (Tensor.indexedDirectSum (fun i ↦
        (dwz63SegmentedFineFiber K n m seg alphaTilde (target i)).realize)) := by
  simp only [← dwz63SegmentedFineFiber_eq_fiberSelect]
  exact dwz63_indexedDirectSum_coarseWord_restricts_fineFiberSelect K n target htarget
    ((SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n seg)

end

end AlgebraicComplexity.Examples
