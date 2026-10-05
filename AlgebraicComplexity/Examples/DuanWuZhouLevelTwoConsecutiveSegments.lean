/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedConsecutiveBlocks
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentationData

set_option autoImplicit false

/-!
# Section 6.3's leaf on consecutive segments

Layer 4 (`AlgebraicComplexity/Examples/`).  `dwz63Seg` labels a position by the coarse cell sitting
there (`Examples/DuanWuZhouLevelTwoSegmentationData.lean`), so the fifteen segments are *scattered*
through the reference word.  The regional division
(`MatrixMultiplication/SegmentedLocalizedDivisionIterated.lean`) needs them **consecutive**.  This
module supplies the fifteen-region block list and the permutation that sorts the leaf onto it.

## What the fifteen blocks are

Block `t` holds every position of cell `t`: `multiplicity (dwz63Seg K n wRef) t` of them, which by
`card_fiber_dwz63Seg` is the number of letters of `wRef` in cell `t`.  Its prescribed per-segment
type is `alphaTilde t` on its own segment and the *zero* type on the other fourteen --- the shape
`SegmentedSplitRestriction.keeps_const_seg_iff` needs, so that the region's factor is a
one-segment power.  Summing the fifteen types pointwise gives back `alphaTilde`
(`dwz63_parentType_consecutiveBlocks`), which is `claim:degen`'s hypothesis.

`SegmentRegionSpec.size` counts *additional* positions, so block `t` has size
`multiplicity … t - 1` and every block must be nonempty.  That is why
`dwz63_exists_consecutiveBlocks` takes `0 < multiplicity (dwz63Seg K n wRef) t`: a cell missing
from the reference word has no region to peel.  For the section 6.3 reference word the hypothesis
is satisfiable because all fifteen `dwz63Alpha` entries are strictly positive
(`dwz63Alpha_pos`), and `card_fiber_dwz63Seg` turns segment size into cell multiplicity.

## Why the statements are in the raw `segmentedLocalizedSplittingPower` spelling

`dwz63SegmentedFineFiber K n 15 seg alphaTilde target` --- and hence `dwz63ReferenceLeaf` --- **is**
`((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower cwSquareDegreeMap
n 15 seg (SegmentedSplitRestriction.ofLeg Leg.Z alphaTilde) target` by definition, so the raw
spelling applies to the reference leaf with no bridge, exactly as the fine-cell fusion does for
`select`.  Keeping the raw spelling also keeps this module's import closure clear of the hashing
stack, which it has no business depending on.

## The length is `SegmentRegionBlock.total`, not a cast

`dwz63_referenceLeaf_isomorphic_consecutive` quantifies over the blocks and reads the word length
off them.  `dwz63_exists_consecutiveBlocks` hands a client the blocks *existentially* together with
`total = n`; because the bound blocks then have closed types, `subst` moves `n` to
`SegmentRegionBlock.total b rest` and no `Fin` cast is ever introduced.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `hole_lemma.tex` and `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-- **All fifteen section 6.3 cell masses are strictly positive.**  This is what makes every one of
the fifteen segments of a typical reference word nonempty, hence peelable. -/
theorem dwz63Alpha_pos (c : Fin 15) : 0 < dwz63Alpha c := by
  revert c
  decide

section Blocks

variable (K : Type u) [CommRing K]

/-- **One of the fifteen consecutive regions of the section 6.3 leaf.**  Region `t` holds the
positions of cell `t`, prescribes `alphaTilde t` on segment `t` and the zero type elsewhere, and
carries the weight `value t`. -/
noncomputable def dwz63ConsecutiveBlock (n : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ) (value : Fin 15 → ℝ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) (t : Fin 15) :
    SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15 where
  size := WordType.multiplicity (dwz63Seg K n wRef) t - 1
  type := fun t' ↦ if t' = t then alphaTilde t else 0
  value := value t
  label := t

/-- The fourteen regions after the first, in cell order. -/
noncomputable def dwz63ConsecutiveBlocks (n : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ) (value : Fin 15 → ℝ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :
    List (SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15) :=
  [dwz63ConsecutiveBlock K n alphaTilde value wRef 1,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 2,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 3,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 4,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 5,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 6,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 7,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 8,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 9,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 10,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 11,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 12,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 13,
    dwz63ConsecutiveBlock K n alphaTilde value wRef 14]

variable (n : ℕ) (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ) (value : Fin 15 → ℝ)
  (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)

/-- Every one of the fifteen regions is a `dwz63ConsecutiveBlock`. -/
theorem dwz63_mem_consecutiveBlocks :
    ∀ u ∈ dwz63ConsecutiveBlock K n alphaTilde value wRef 0 ::
        dwz63ConsecutiveBlocks K n alphaTilde value wRef,
      ∃ t : Fin 15, u = dwz63ConsecutiveBlock K n alphaTilde value wRef t := by
  intro u hu
  simp only [dwz63ConsecutiveBlocks, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  exacts
    [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩, ⟨6, h⟩, ⟨7, h⟩,
    ⟨8, h⟩, ⟨9, h⟩, ⟨10, h⟩, ⟨11, h⟩, ⟨12, h⟩, ⟨13, h⟩, ⟨14, h⟩]

/-- **The fifteen regions have exactly the segmentation's multiplicity profile.**  Each block
contributes its own cell's count and nothing to the other fourteen. -/
theorem dwz63_multiplicityProfile_consecutiveBlocks
    (hpos : ∀ t, 0 < WordType.multiplicity (dwz63Seg K n wRef) t) :
    SegmentRegionBlock.multiplicityProfile
        (dwz63ConsecutiveBlock K n alphaTilde value wRef 0)
        (dwz63ConsecutiveBlocks K n alphaTilde value wRef) =
      WordType.multiplicity (dwz63Seg K n wRef) := by
  have hsucc : ∀ t : Fin 15,
      WordType.multiplicity (dwz63Seg K n wRef) t - 1 + 1 =
        WordType.multiplicity (dwz63Seg K n wRef) t :=
    fun t ↦ Nat.succ_pred_eq_of_pos (hpos t)
  funext t
  fin_cases t <;>
    simp [dwz63ConsecutiveBlocks, dwz63ConsecutiveBlock, hsucc]

/-- **The fifteen regional types sum to `alphaTilde`.**  This is `claim:degen`'s hypothesis on the
restricted leg. -/
theorem dwz63_parentType_consecutiveBlocks :
    SegmentRegionSpec.parentType
        (dwz63ConsecutiveBlock K n alphaTilde value wRef 0).toSegmentRegionSpec
        (SegmentRegionBlock.specs (dwz63ConsecutiveBlocks K n alphaTilde value wRef)) =
      alphaTilde := by
  funext t
  fin_cases t <;>
    simp [dwz63ConsecutiveBlocks, dwz63ConsecutiveBlock, SegmentRegionBlock.specs]

/-- **A proportionally typed reference word meets every one of the fifteen cells.**

This is where `dwz63Alpha_pos` is spent: at any positive scale the section 6.3 proportional type
gives every segment a positive size, so all fifteen regions are peelable and
`dwz63_exists_consecutiveBlocks` applies. -/
theorem dwz63_multiplicity_seg_pos (scale : ℕ) (hscale : 0 < scale)
    (htype : ∀ t, WordType.multiplicity (dwz63Seg K n wRef) t = dwz63Alpha t * scale) (t : Fin 15)
      :
    0 < WordType.multiplicity (dwz63Seg K n wRef) t := by
  rw [htype t]
  exact Nat.mul_pos (dwz63Alpha_pos t) hscale

/-- The same statement as a segment size, through `card_fiber_dwz63Seg`: segment `t` of the
reference word holds at least one position. -/
theorem dwz63_card_fiber_seg_pos (scale : ℕ) (hscale : 0 < scale)
    (htype : ∀ t, WordType.multiplicity (dwz63Seg K n wRef) t = dwz63Alpha t * scale) (t : Fin 15)
      :
    0 < (Finset.univ.filter fun i ↦ dwz63Seg K n wRef i = t).card := by
  rw [card_fiber_dwz63Seg]
  exact dwz63_multiplicity_seg_pos K n wRef scale hscale htype t

/-- **The fifteen consecutive regions of the section 6.3 leaf, packaged.**

The blocks are handed over existentially, so a client can `subst` the length equation and work at
`SegmentRegionBlock.total` with no `Fin` cast.  The last conjunct records what each region is: its
type is `alphaTilde` on its own segment and zero elsewhere, its weight is `value` at its own cell,
and it holds exactly that cell's positions. -/
theorem dwz63_exists_consecutiveBlocks
    (hpos : ∀ t, 0 < WordType.multiplicity (dwz63Seg K n wRef) t) :
    ∃ (b : SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15)
      (rest : List (SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15)),
      SegmentRegionBlock.total b rest = n ∧
      SegmentRegionBlock.multiplicityProfile b rest =
        WordType.multiplicity (dwz63Seg K n wRef) ∧
      SegmentRegionSpec.parentType b.toSegmentRegionSpec (SegmentRegionBlock.specs rest) =
        alphaTilde ∧
      ∀ u ∈ b :: rest,
        u.type = (fun t' ↦ if t' = u.label then alphaTilde u.label else 0) ∧
        u.value = value u.label ∧
        u.size + 1 = WordType.multiplicity (dwz63Seg K n wRef) u.label := by
  refine ⟨dwz63ConsecutiveBlock K n alphaTilde value wRef 0,
    dwz63ConsecutiveBlocks K n alphaTilde value wRef, ?_,
    dwz63_multiplicityProfile_consecutiveBlocks K n alphaTilde value wRef hpos,
    dwz63_parentType_consecutiveBlocks K n alphaTilde value wRef, ?_⟩
  · exact SegmentRegionBlock.total_eq_of_multiplicityProfile _ _ (dwz63Seg K n wRef)
      (dwz63_multiplicityProfile_consecutiveBlocks K n alphaTilde value wRef hpos)
  · intro u hu
    obtain ⟨t, rfl⟩ := dwz63_mem_consecutiveBlocks K n alphaTilde value wRef u hu
    exact ⟨rfl, rfl, Nat.succ_pred_eq_of_pos (hpos t)⟩

end Blocks

/-! ## Sorting the leaf onto consecutive segments -/

section Sorting

variable (K : Type u) [CommRing K]

/-- **The section 6.3 leaf is isomorphic to a consecutive-segment leaf.**

The permutation comes from `SegmentRegionBlock.exists_perm_comp_eq_seg` --- the scattered
segmentation and the canonical consecutive one have the same multiplicity profile, hence differ by
a relabelling of positions --- and
`Tensor.Isomorphic.segmentedLocalizedSplittingPower_position` absorbs it, moving the segmentation
and the coarse target together.  The right-hand leaf's segmentation is exactly
`SegmentRegionBlock.seg`, whose `segmentationLeft` / `segmentationRight` recursion is the one the
regional division peels. -/
theorem dwz63_referenceLeaf_isomorphic_consecutive
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (b : SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15)
    (rest : List (SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support)
      (SegmentRegionBlock.total b rest))
    (hmult : WordType.multiplicity
        (dwz63Seg K (SegmentRegionBlock.total b rest) wRef) =
      SegmentRegionBlock.multiplicityProfile b rest) :
    ∃ σ : Equiv.Perm (Fin (SegmentRegionBlock.total b rest + 1)),
      Isomorphic
        (((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap (SegmentRegionBlock.total b rest) 15
          (dwz63Seg K (SegmentRegionBlock.total b rest) wRef)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
          (positiveSupportWordBlockAddress
            ((cwSquarePartitionedTensor K dwz63Q).support)
            (SegmentRegionBlock.total b rest) wRef)).realize
        (((cwPartitionedTensor K dwz63Q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap (SegmentRegionBlock.total b rest) 15
          (SegmentRegionBlock.seg b rest)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
          (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
            (SegmentRegionBlock.total b rest) σ
            (positiveSupportWordBlockAddress
              ((cwSquarePartitionedTensor K dwz63Q).support)
              (SegmentRegionBlock.total b rest) wRef))).realize := by
  obtain ⟨σ, hσ⟩ := SegmentRegionBlock.exists_perm_comp_eq_seg b rest
    (dwz63Seg K (SegmentRegionBlock.total b rest) wRef) hmult
  refine ⟨σ, ?_⟩
  have h := Tensor.Isomorphic.segmentedLocalizedSplittingPower_position
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap
    (SegmentRegionBlock.total b rest) 15
    (dwz63Seg K (SegmentRegionBlock.total b rest) wRef)
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support)
      (SegmentRegionBlock.total b rest) wRef) σ
  rw [hσ] at h
  exact h

end Sorting

end AlgebraicComplexity.Examples
