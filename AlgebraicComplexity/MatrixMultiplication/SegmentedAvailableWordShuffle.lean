/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedAvailableWord
import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling

/-!
# Claim 1 for segmented available blocks, and the segmented shuffling action

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `RestrictedSplittingShuffle.lean:95-108`
proves `[DuanWuZhou2022]`'s Claim 1 for the pooled type: a position permutation preserves the
empirical type of a block word, so the full symmetric group permutes the available blocks.  For the
segmented type that is **false** for an arbitrary permutation --- moving a position out of its
segment changes both segments' types --- and true exactly for the segment-preserving permutations,
which is why `hole_lemma.tex:72-74` takes the group `Sym[n_1] x ... x Sym[n_m]` and why Claim 1's
proof there turns on the destination "staying within the region" (`:95-101`).

This module proves that, and uses it to build the action itself.  Neither depends on the author's
shuffle-independence question: **Claims 1 and 2 are un-gated, only Claim 3 is gated.**

## What this sharpens

`SegmentedAvailableWord.lean` had to state its Claim-3 hypothesis as "there exists a uniform family
on the segmented available words".  With the action in hand the hypothesis becomes a concrete
finite counting statement about **one specific action** --- `SegmentedFiberIndependence` --- which
is what `[DuanWuZhou2022]`'s `∏_t ∏_{k'} (α̃_t(k') n_t)!` (`hole_lemma.tex:111-120`) computes, and
which `HoleRepair.UniformOnParts.ofTargetIndependentFiber` turns back into the family.  That is a
strictly better shape both for discharging it and for putting the author's question precisely.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

section ClaimOne

variable {I : Type w} [DecidableEq I] {n m : ℕ}

/-- **Claim 1, segmented.**  A position permutation that preserves segments preserves every
segment's empirical type.  The hypothesis `hperm` is exactly `hole_lemma.tex:95-101`'s "stays
within the region", and it is what fails for a permutation that crosses segments. -/
theorem segmentMultiplicity_comp_perm (seg : Fin n → Fin m)
    (σ : Equiv.Perm (Fin n)) (hperm : ∀ i, seg (σ i) = seg i)
    (word : Fin n → I) (t : Fin m) :
    segmentMultiplicity seg (word ∘ σ) t = segmentMultiplicity seg word t := by
  classical
  funext a
  unfold segmentMultiplicity
  refine Finset.card_nbij' (fun i ↦ σ i) (fun j ↦ σ.symm j) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hperm i]; exact hi.2.1, hi.2.2⟩
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_filter] at hj
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hs := hperm (σ.symm j)
      rw [Equiv.apply_symm_apply] at hs
      rw [← hs]
      exact hj.2.1
    · show word (σ (σ.symm j)) = a
      rw [Equiv.apply_symm_apply]
      exact hj.2.2
  · intro i _
    simp
  · intro j _
    simp

end ClaimOne

section Action

variable {I : Type w} [Fintype I] [DecidableEq I] {n m : ℕ}

omit [Fintype I] in
/-- **Claim 1 on the words themselves**: a segmented shuffle preserves segmented availability. -/
theorem segmentMultiplicity_positiveWordPositionEquiv
    (seg : Fin (n + 1) → Fin m) (φ : SegmentPerm seg)
    (word : PositiveWord I n) (t : Fin m) :
    segmentMultiplicity seg
        (positiveWordEquiv I n
          (positiveWordPositionEquiv I n (segmentPermToPerm seg φ) word)) t =
      segmentMultiplicity seg (positiveWordEquiv I n word) t := by
  rw [positiveWordEquiv_position_apply]
  exact segmentMultiplicity_comp_perm seg (segmentPermToPerm seg φ)
    (seg_segmentPermToPerm seg φ) (positiveWordEquiv I n word) t

/-- **The segmented shuffling action.**  `[DuanWuZhou2022]`'s `Sym[n_1] x ... x Sym[n_m]` acting on
the available small blocks of a segmented restricted-splitting power.  Compare the committed
pooled `availableWordShuffle` (`RestrictedSplittingShuffle.lean:194`), whose group is the full
symmetric group. -/
noncomputable def segmentedAvailableWordShuffle
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (φ : SegmentPerm seg) :
    Equiv.Perm (SegmentedAvailableWord seg α) :=
  (positiveWordPositionEquiv I n (segmentPermToPerm seg φ)).subtypePerm fun word ↦ by
    constructor
    · intro h t
      have hval := h t
      rwa [segmentMultiplicity_positiveWordPositionEquiv] at hval
    · intro h t
      rw [segmentMultiplicity_positiveWordPositionEquiv]
      exact h t

omit [Fintype I] in
@[simp] theorem segmentedAvailableWordShuffle_val
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (φ : SegmentPerm seg)
    (word : SegmentedAvailableWord seg α) :
    (segmentedAvailableWordShuffle seg α φ word).1 =
      positiveWordPositionEquiv I n (segmentPermToPerm seg φ) word.1 := rfl

/-! ## The gated hypothesis, sharpened -/

/-- **The Claim-3 analogue as a concrete finite count.**

For a fixed source block, the number of segmented shuffles reaching a given target does not depend
on the target.  This is `[DuanWuZhou2022]`'s `hole_lemma.tex:111-120` --- there the common value is
computed as `∏_t ∏_{k'} (α̃_t(k') n_t)!`, though
`HoleRepair.UniformOnParts.ofTargetIndependentFiber` shows no formula is needed.

**This is the only statement still gated** by whether the per-component shuffles in
`∑_t η_t ≥ Nℓ + 1` are independent; Claims 1 and 2 above are not. -/
def SegmentedFiberIndependence (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) : Prop :=
  ∀ a b b' : SegmentedAvailableWord seg α,
    (Finset.univ.filter fun φ : SegmentPerm seg ↦
        segmentedAvailableWordShuffle seg α φ a = b).card =
      (Finset.univ.filter fun φ : SegmentPerm seg ↦
        segmentedAvailableWordShuffle seg α φ a = b').card

/-- The sharpened hypothesis supplies the family the Hole Lemma consumes. -/
noncomputable def segmentedShuffleUniformity_of_fiberIndependence
    {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ}
    (h : SegmentedFiberIndependence seg α) : SegmentedShuffleUniformity seg α :=
  HoleRepair.UniformOnParts.ofTargetIndependentFiber
    (segmentedAvailableWordShuffle seg α) h

end Action

end AlgebraicComplexity
