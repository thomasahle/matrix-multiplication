/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellZeroLeg
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedHoleRepair

set_option autoImplicit false

/-!
# The one-segment localized power, and what its support is

Layer 4 (`AlgebraicComplexity/Examples/`).  Stage (2) of the `[DuanWuZhou2022]` section 6.3 value
route fuses **one cell** of the reference leaf.  The subject is the *segmented* spelling --- the
one-segment instance of `PartitionedTensor.segmentedLocalizedSplittingPower` --- so that stage (D)
can factorise the leaf by a segmentation product inside a single family rather than bridging two
spellings per cell.

This module settles what that instance's support is.  The answer is **not definitional**: at one
segment the keep predicate still carries the `∀ t : Fin 1` wrapper of
`SegmentedSplitRestriction.Keeps` and the vacuous `seg i = t` conjunct inside `segmentMultiplicity`,
so the object is only *propositionally* the fine power selected by "coarsens to the target" and
"has pooled `Z`-type `α`".  `dwz63_mem_cellPower_support_iff` is that equivalence, proved from the
committed `mem_segmentedLocalizedSplittingPower_support` and `segmentMultiplicity_one`.

With it, the three support hypotheses of the one-slice fusion --- `hz` from
`Examples/DuanWuZhouLevelTwoFineCellZeroLeg.lean`, `hx`/`hy` from
`Examples/DuanWuZhouLevelTwoFineCellSupport.lean` --- can be discharged directly against the
segmented spelling, with no second object anywhere in the development.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- **The support of the one-segment localized power.**  An address survives exactly when it is an
address of the fine power, coarsens to the target on every leg, and its `Z` word has pooled type
`α`.  The `Fin 1` segmentation contributes nothing beyond the pooled type, but it is not
definitionally absent --- hence a lemma rather than `rfl`. -/
theorem dwz63_mem_cellPower_support_iff (K : Type u) [CommRing K] (q n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)) :
    s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support ↔
      s ∈ (((cwPartitionedTensor K q).positivePower 1).positivePower n).support ∧
        (∀ c, positiveWordMap (cwSquareDegreeMap c) n (s c) = target c) ∧
        WordType.multiplicity
          (positiveWordEquiv (PositiveWord CWBlock 1) n (s Leg.Z)) = α := by
  rw [PartitionedTensor.mem_segmentedLocalizedSplittingPower_support]
  constructor
  · rintro ⟨hmem, hkeep⟩
    refine ⟨hmem, fun c ↦ (hkeep c).1, ?_⟩
    have hzk := (hkeep Leg.Z).2 0
    rw [SegmentedSplitRestriction.ofLeg_self] at hzk
    rw [← segmentMultiplicity_one
      (positiveWordEquiv (PositiveWord CWBlock 1) n (s Leg.Z))]
    exact hzk
  · rintro ⟨hmem, hcoarse, htype⟩
    refine ⟨hmem, fun c ↦ ⟨hcoarse c, ?_⟩⟩
    intro t
    have ht : t = 0 := Fin.eq_zero t
    subst ht
    cases c with
    | X => simp [SegmentedSplitRestriction.ofLeg]
    | Y => simp [SegmentedSplitRestriction.ofLeg]
    | Z =>
        rw [SegmentedSplitRestriction.ofLeg_self]
        rw [segmentMultiplicity_one]
        exact htype

end AlgebraicComplexity.Examples
