/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutLeafFiber
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutDominationInputs

set_option autoImplicit false

/-!
# The broken standard-form leaf of `𝒯^{(1)}`, in the reference frame

Layer 4 (`AlgebraicComplexity/Examples/`).  The last step of the re-issue: each fibre of image
149's grouping reaches **one** broken copy of `𝒯^*` --- the same copy for every retained triple,
carried by the reference word, with holes.  `[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-102`:

>  … resulting in `𝒯^{(2)}|_{X_I,Y_J,Z_K}` being a broken copy of `𝒯^*` with some holes in
> its
> `Z`-variables.  (`:100`)
> One can see that `𝒯^*` exactly matches `def:standard_form_tensor` with parameters
>  `⟨n α(i,j,k), i, j, k, α̃_{i,j,k}⟩`.  This will allow us to apply the hole lemma …
> (`:102`)

The hole lemma the paper then applies is `cor:hole_lemma`
(`papers/sources/2210.10173/hole_lemma.tex:159-168`), which needs the broken copies to be copies of
**one** standard-form tensor; that is why the fibres are transported into the reference frame here.
The tree has the same statement on the uncut preimage ambient
(`Examples/DuanWuZhouLevelTwoPreimageLeaf.lean:321`, image 85), which the R1 repair supersedes and
which is neither edited nor imported.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:86, 98-102` and `hole_lemma.tex:159-168`, at the
section 6.3 instance (`global_value.tex:332-378`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u

noncomputable section

variable {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- **Segment counts are frame-independent.**

Moving positions by one permutation in both the segmentation and the word leaves every segment
count unchanged; the reference frame of `global_value.tex:270-320` is therefore immaterial to
availability. -/
theorem dwz63_segmentMultiplicity_frameTransport (K : Type u) [CommRing K]
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (σ : Equiv.Perm (Fin (n + 1))) (v : PositiveWord (PositiveWord CWBlock 1) n)
    (t : Fin 15) :
    segmentMultiplicity
        (dwz63Seg K n
          (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef))
        (positiveWordEquiv (PositiveWord CWBlock 1) n
          (positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ v)) t =
      segmentMultiplicity (dwz63Seg K n wRef)
        (positiveWordEquiv (PositiveWord CWBlock 1) n v) t := by
  rw [dwz63Seg_positionEquiv, positiveWordEquiv_position_apply,
    segmentMultiplicity_comp_perm_general]

/-- **The reference holes transport onto the isolation holes** (`global_value.tex:86`, `:100`).

The two families are the same set of `Z`-words, read in the two frames: image 145's
`dwz63CutReferenceHoles` in the reference frame of the word `wRef`, and
`dwz63CutIsolationHoles` in the triple's own.

Proof sketch: transport availability along `perm a` in both directions with
`dwz63_segmentMultiplicity_frameTransport`, and match the witnessing addresses. -/
theorem dwz63CutReferenceHoles_image (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1))) (a : retained) :
    ((dwz63CutReferenceHoles K retained a₀ s alphaTilde wRef perm a).image Subtype.val).image
        (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a)) =
      (dwz63CutIsolationHoles K retained a₀ s
        (dwz63Seg K n (positiveWordPositionEquiv
          ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef))
        alphaTilde a).image Subtype.val := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    obtain ⟨z, hz, hzv⟩ := Finset.mem_image.mp hv
    obtain ⟨zw, hzavail⟩ := z
    obtain ⟨other, hother, hotherZ, hne⟩ := (Finset.mem_filter.mp hz).2
    have hwz : w = positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) zw := by
      rw [← hvw, ← hzv]
    subst hwz
    have havail : ∀ t, segmentMultiplicity
        (dwz63Seg K n (positiveWordPositionEquiv
          ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef))
        (positiveWordEquiv (PositiveWord CWBlock 1) n
          (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) zw)) t =
        alphaTilde t := by
      intro t
      rw [dwz63_segmentMultiplicity_frameTransport K wRef (perm a) zw t]
      exact hzavail t
    refine Finset.mem_image.mpr ⟨⟨_, havail⟩, ?_, rfl⟩
    exact (mem_dwz63CutIsolationHoles K a₀ s _ alphaTilde a _).mpr
      ⟨other, hother, hotherZ, hne⟩
  · intro hw
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hw
    obtain ⟨other, hother, hotherZ, hne⟩ :=
      (mem_dwz63CutIsolationHoles K a₀ s _ alphaTilde a z).mp hz
    obtain ⟨zw, hzavail⟩ := z
    have havail : ∀ t, segmentMultiplicity (dwz63Seg K n wRef)
        (positiveWordEquiv (PositiveWord CWBlock 1) n
          ((positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a)).symm zw)) t =
        alphaTilde t := by
      intro t
      rw [← dwz63_segmentMultiplicity_frameTransport K wRef (perm a)
        ((positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a)).symm zw) t,
        Equiv.apply_symm_apply]
      exact hzavail t
    refine Finset.mem_image.mpr
      ⟨(positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a)).symm zw, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨⟨_, havail⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨other, hother, by rw [hotherZ, Equiv.apply_symm_apply], hne⟩⟩, rfl⟩
    · rw [Equiv.apply_symm_apply]
      exact hzw

/-- **The grouped fibre of `𝒯^{(2)}` reaches the one broken reference leaf** (`:98-102`).

Select by the segment types --- landing, by `dwz63CutGrouping_fiber_select_eq`, on the localized
broken leaf over the triple's own coarse word --- then transport to the reference word, holes and
all.  The result is the input `cor:hole_lemma` (`hole_lemma.tex:159-168`) consumes.

Proof sketch: `Restricts.partitionedSelect`, then the fibre/leaf identity of image 150 (whose
`hseg` is `dwz63Seg_eq_cellWordOfAddress` composed with the reference-frame equation `hperm`), then
the position isomorphism `dwz63_brokenFineLeaf_isomorphic_position` rewritten by
`dwz63CutReferenceHoles_image`. -/
theorem dwz63_cutFiber_restricts_brokenReferenceLeaf (K : Type u) [CommRing K]
    (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _))
    {alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ}
    (hS : (dwz63SplitPair s).splitCount = alphaTilde)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ b : retained,
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm b) wRef) =
        (b : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a : retained) :
    Restricts ((dwz63CutGrouping K a₀ s hX hY).fiber a).realize
      (dwz63BrokenFineLeaf K n 15 (dwz63Seg K n wRef) alphaTilde
        (positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)
        ((dwz63CutReferenceHoles K retained a₀ s alphaTilde wRef perm a).image
          Subtype.val)).realize := by
  classical
  have hseg : dwz63Seg K n (positiveWordPositionEquiv
      ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
      dwz63CellWordOfAddress (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) := by
    rw [dwz63Seg_eq_cellWordOfAddress, hperm a]
  have hsel := Tensor.Restricts.partitionedSelect
    ((dwz63CutGrouping K a₀ s hX hY).fiber a)
    ((SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n
      (dwz63Seg K n (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef)))
  rw [dwz63CutGrouping_fiber_select_eq K a₀ s hX hY hS a _ hseg, ← hperm a] at hsel
  refine hsel.trans (Tensor.Isomorphic.restricts ?_)
  have hiso := dwz63_brokenFineLeaf_isomorphic_position K n alphaTilde wRef (perm a)
    ((dwz63CutReferenceHoles K retained a₀ s alphaTilde wRef perm a).image Subtype.val)
  rw [dwz63CutReferenceHoles_image K a₀ s alphaTilde wRef perm a] at hiso
  exact hiso.symm

end

end AlgebraicComplexity.Examples
