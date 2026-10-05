/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.LegwiseHashingExtraction

/-!
# Two-leg isolation by affine hashing

The exceptional Coppersmith--Winograd `112` argument must make the surviving block triples
distinct on the X and Y legs while deliberately allowing several triples to share one Z word.
Those shared-Z fibers are the C-tensors that provide the extra value gain.

This module proves the reusable combinatorial extraction theorem needed for that situation.  It
uses the same affine progression-free filter and collision proxy as the all-three-leg theorem,
but lists as competitors only targets sharing X or Y.  The selected family is therefore
injective on X and Y, with no assertion (and no accidental zeroing) on Z.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

/-- Two legal triples conflict for C-tensor extraction when they share their X word or their Y
word.  Sharing only Z is permitted and is the source of the later C-tensor fibers. -/
def SharesXY (left right : LegalTriple R ι target) : Prop :=
  left.xIndex = right.xIndex ∨ left.yIndex = right.yIndex

/-- Other targets sharing X or Y with a fixed target. -/
noncomputable def xyCompetitors
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    Finset (LegalTriple R ι target) := by
  classical
  exact (targets.erase triple).filter (SharesXY triple)

/-- Collision proxies for all other targets sharing X or Y with a fixed target. -/
noncomputable def xyCompetitorYIndices
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    Finset (ι → R) := by
  classical
  exact (xyCompetitors targets triple).image (collisionProxy triple)

/-- The two-leg proxy count is at most the sum of the X- and Y-fiber sizes.  Proof sketch: the
image has no more elements than its source, and every XY competitor belongs to one of the two
leg fibers. -/
theorem card_xyCompetitorYIndices_le_add_legFibers
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    (xyCompetitorYIndices targets triple).card ≤
      (legFiber targets triple .X).card + (legFiber targets triple .Y).card := by
  classical
  calc
    (xyCompetitorYIndices targets triple).card ≤
        (xyCompetitors targets triple).card := Finset.card_image_le
    _ ≤ (legFiber targets triple .X ∪ legFiber targets triple .Y).card := by
      apply Finset.card_le_card
      intro other hother
      obtain ⟨herase, hshare⟩ := Finset.mem_filter.mp hother
      have htarget : other ∈ targets := (Finset.mem_erase.mp herase).2
      rcases hshare with hx | hy
      · exact Finset.mem_union_left _ <|
          (mem_legFiber targets triple other .X).2 ⟨htarget, hx.symm⟩
      · exact Finset.mem_union_right _ <|
          (mem_legFiber targets triple other .Y).2 ⟨htarget, hy.symm⟩
    _ ≤ (legFiber targets triple .X).card +
        (legFiber targets triple .Y).card := Finset.card_union_le _ _

/-- A common upper bound on the X- and Y-fiber sizes gives twice that bound on the proxy family. -/
theorem card_xyCompetitorYIndices_le_two_mul
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target)
    (d : ℕ)
    (hX : (legFiber targets triple .X).card ≤ d)
    (hY : (legFiber targets triple .Y).card ≤ d) :
    (xyCompetitorYIndices targets triple).card ≤ 2 * d := by
  apply (card_xyCompetitorYIndices_le_add_legFibers targets triple).trans
  omega

/-- Every genuine XY competitor contributes its collision proxy to the two-leg proxy family. -/
theorem collisionProxy_mem_xyCompetitorYIndices
    (targets : Finset (LegalTriple R ι target))
    {triple other : LegalTriple R ι target}
    (hother : other ∈ targets) (hne : other ≠ triple)
    (hshare : SharesXY triple other) :
    collisionProxy triple other ∈ xyCompetitorYIndices targets triple := by
  classical
  rw [xyCompetitorYIndices, Finset.mem_image]
  refine ⟨other, ?_, rfl⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_erase.mpr ⟨hne, hother⟩, hshare⟩

/-- Every two-leg collision proxy differs from the intended Y word. -/
theorem yIndex_ne_of_mem_xyCompetitorYIndices
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target)
    {J' : ι → R} (hJ' : J' ∈ xyCompetitorYIndices targets triple) :
    J' ≠ triple.yIndex := by
  classical
  rw [xyCompetitorYIndices, Finset.mem_image] at hJ'
  obtain ⟨other, hother, rfl⟩ := hJ'
  exact collisionProxy_ne triple other
    (Finset.mem_erase.mp (Finset.mem_filter.mp hother).1).1

/-- Targets selected by affine hashing and isolated only against X/Y competitors. -/
noncomputable def xyIsolatedTargets
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    Finset (LegalTriple R ι target) :=
  Seed.isolatedTargets targets B LegalTriple.xIndex LegalTriple.yIndex
    (xyCompetitorYIndices targets) seed

/-- Two-leg-isolated targets survive the ordinary three-leg progression-free hash filter. -/
theorem xyIsolatedTargets_subset_filteredTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) :
    xyIsolatedTargets targets B seed ⊆ filteredTargets targets B seed := by
  classical
  intro triple htriple
  have himage : triple ∈ Seed.isolatedTargets targets B LegalTriple.xIndex
      LegalTriple.yIndex (xyCompetitorYIndices targets) seed := by
    simpa [xyIsolatedTargets] using htriple
  obtain ⟨⟨other, b⟩, hincidence, hfst⟩ := Finset.mem_image.mp himage
  simp only at hfst
  subst other
  have hfilter := Finset.mem_filter.mp hincidence
  have htarget : triple ∈ targets := (Finset.mem_product.mp hfilter.1).1
  have hb : b ∈ B := (Finset.mem_product.mp hfilter.1).2
  have hcommon := hfilter.2.1
  have hZ : seed.zHash target triple.zIndex = b :=
    Seed.zHash_eq_of_commonBucket seed triple.xIndex triple.yIndex triple.zIndex
      target b triple.legal hcommon
  apply Finset.mem_filter.mpr
  exact ⟨htarget, by
    exact ⟨by simpa [hcommon.1] using hb,
      by simpa [hcommon.2] using hb,
      by simpa [hZ] using hb⟩⟩

/-- An XY-isolated target is the unique filtered target sharing either its X word or its Y word.
Proof sketch: a shared word forces the two triples into the same hash bucket, while the second
triple's collision proxy is forbidden by the isolation event. -/
theorem eq_of_mem_xyIsolatedTargets_of_mem_filteredTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι)
    {triple other : LegalTriple R ι target}
    (htriple : triple ∈ xyIsolatedTargets targets B seed)
    (hother : other ∈ filteredTargets targets B seed)
    (hshare : SharesXY triple other) :
    other = triple := by
  classical
  by_contra hne
  have himage : triple ∈ Seed.isolatedTargets targets B LegalTriple.xIndex
      LegalTriple.yIndex (xyCompetitorYIndices targets) seed := by
    simpa [xyIsolatedTargets] using htriple
  obtain ⟨⟨triple', b⟩, hincidence, hfst⟩ := Finset.mem_image.mp himage
  simp only at hfst
  subst triple'
  have hfilter := Finset.mem_filter.mp hincidence
  have htripleTarget : triple ∈ targets := (Finset.mem_product.mp hfilter.1).1
  have htripleEvent := hfilter.2
  change seed ∈ Seed.isolatedSeeds triple.xIndex triple.yIndex
      (xyCompetitorYIndices targets triple) b at htripleEvent
  have hotherData := (mem_filteredTargets targets B hB seed other).mp hother
  obtain ⟨hotherTarget, c, _hcB, hotherCommon⟩ := hotherData
  have hproxyMem : collisionProxy triple other ∈
      xyCompetitorYIndices targets triple :=
    collisionProxy_mem_xyCompetitorYIndices targets hotherTarget hne hshare
  have hnot := htripleEvent.2 _ hproxyMem
  apply hnot
  have hcb : c = b := by
    rcases hshare with hx | hy
    · exact commonBucket_eq_of_legIndex_eq seed triple other b c htripleEvent.1
        hotherCommon .X hx.symm
    · exact commonBucket_eq_of_legIndex_eq seed triple other b c htripleEvent.1
        hotherCommon .Y hy.symm
  unfold collisionProxy
  split_ifs with hx
  · exact hotherCommon.2.trans hcb
  · rw [Seed.yHash_transportXAlternative_eq_xHash seed triple.xIndex
      triple.yIndex other.xIndex b htripleEvent.1]
    exact hotherCommon.1.trans hcb

/-- The selected target family is injective on X. -/
theorem xIndex_injectiveOn_xyIsolatedTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι) :
    Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
      (xyIsolatedTargets targets B seed : Set (LegalTriple R ι target)) := by
  intro triple htriple other hother hx
  exact (eq_of_mem_xyIsolatedTargets_of_mem_filteredTargets targets B hB seed
    htriple (xyIsolatedTargets_subset_filteredTargets targets B seed hother)
    (Or.inl hx)).symm

/-- The selected target family is injective on Y. -/
theorem yIndex_injectiveOn_xyIsolatedTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι) :
    Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.yIndex)
      (xyIsolatedTargets targets B seed : Set (LegalTriple R ι target)) := by
  intro triple htriple other hother hy
  exact (eq_of_mem_xyIsolatedTargets_of_mem_filteredTargets targets B hB seed
    htriple (xyIsolatedTargets_subset_filteredTargets targets B seed hother)
    (Or.inr hy)).symm

/-- Complete finite two-leg hashing extraction.  Under the usual degree condition, one affine
seed selects many filtered targets, injectively on X and Y, while retaining arbitrary shared-Z
fibers for the C-tensor argument. -/
theorem exists_seed_many_xyIsolatedTargets [Fintype R] [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ targets,
      4 * (xyCompetitorYIndices targets triple).card ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * targets.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (xyIsolatedTargets targets B seed).card ∧
        xyIsolatedTargets targets B seed ⊆ filteredTargets targets B seed ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
          (xyIsolatedTargets targets B seed : Set (LegalTriple R ι target)) ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.yIndex)
          (xyIsolatedTargets targets B seed : Set (LegalTriple R ι target)) := by
  classical
  have hdistinct : ∀ triple ∈ targets,
      ∀ J' ∈ xyCompetitorYIndices targets triple, J' ≠ triple.yIndex := by
    intro triple _htriple J' hJ'
    exact yIndex_ne_of_mem_xyCompetitorYIndices targets triple hJ'
  obtain ⟨seed, hcount⟩ := Seed.exists_seed_many_isolatedTargets targets B
    LegalTriple.xIndex LegalTriple.yIndex (xyCompetitorYIndices targets)
    hdistinct hquarter
  refine ⟨seed, ?_, xyIsolatedTargets_subset_filteredTargets targets B seed,
    xIndex_injectiveOn_xyIsolatedTargets targets B hB seed,
    yIndex_injectiveOn_xyIsolatedTargets targets B hB seed⟩
  simpa [xyIsolatedTargets] using hcount

end ProgressionHash.LegalTriple

end AlgebraicComplexity
