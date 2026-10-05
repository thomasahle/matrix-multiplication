/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPreimageGroupedSum
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGroupedLeaf

set_option autoImplicit false

/-!
# The isolated fibre, and the holes Step 2 actually deletes

Two facts about `dwz63PreimageZSupport`, both consequences of the hash's `InjOn` certificates.

**The `.Y` isolation is lossless.**  Two supported addresses sharing a fine `Y`-word share its
coarse image's `Y`-word; the retained family is `Y`-injective, so their coarse images coincide and
they have the same group.  Nothing is deleted (`dwz63PreimageYSupport_eq`), which is what
distinguishes the preimage ambient from a box, where the same isolation is degenerate.

**The `.Z` isolation is Additional Zeroing-Out Step 2.**  What it deletes is exactly the fine
`Z`-words carried by two different retained groups (`mem_dwz63PreimageZSupport`), and
`dwz63IsolationHoles` names that set.  It is not a parameter: the hole family is *defined* by the
isolation, and its members are, by construction, `Z`-words compatible with a competing retained
triple --- rule (i) of `global_value.tex:74-89`.

`[DuanWuZhou2022]`, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

variable {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- **The `.Y` isolation deletes nothing on the preimage ambient.** -/
theorem dwz63PreimageYSupport_eq (K : Type u) [CommRing K] (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _)) :
    dwz63PreimageYSupport K retained a₀ = (dwz63PreimageFine K n retained).support := by
  classical
  refine Finset.Subset.antisymm (groupCompatibilityIsolatedSupport_subset _ _ _ _) ?_
  intro s hs
  rw [dwz63PreimageYSupport, mem_groupCompatibilityIsolatedSupport]
  refine ⟨hs, ?_⟩
  intro other hother hcompat
  rw [mem_dwz63PreimageFine_support] at hs hother
  have hsg := dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
    (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := s) hX
    (a := (⟨_, hs.2⟩ : retained)) rfl
  have hog := dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
    (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := other) hX
    (a := (⟨_, hother.2⟩ : retained)) rfl
  rw [hsg, hog]
  refine Subtype.ext (hY (Finset.mem_coe.mpr hother.2) (Finset.mem_coe.mpr hs.2) ?_)
  show positiveWordMap (cwSquareDegreeMap Leg.Y) n (other Leg.Y) =
    positiveWordMap (cwSquareDegreeMap Leg.Y) n (s Leg.Y)
  rw [hcompat]

/-- **What the `.Z` isolation keeps.** -/
theorem mem_dwz63PreimageZSupport (K : Type u) [CommRing K] (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _))
    (s : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :
    s ∈ dwz63PreimageZSupport K retained a₀ ↔
      s ∈ (dwz63PreimageFine K n retained).support ∧
        ∀ other ∈ (dwz63PreimageFine K n retained).support,
          other Leg.Z = s Leg.Z →
            dwz63PlainCoarseGroup retained
                (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other =
              dwz63PlainCoarseGroup retained
                (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ s := by
  rw [dwz63PreimageZSupport, dwz63PreimageYSupport_eq K a₀ hX hY,
    mem_groupCompatibilityIsolatedSupport]
  exact Iff.rfl

/-- **The holes of Step 2**: the available `Z`-words carried by a group other than `a`. -/
noncomputable def dwz63IsolationHoles (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) {m : ℕ} (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ) (a : retained) :
    Finset (SegmentedAvailableWord seg alphaTilde) := by
  classical
  exact Finset.univ.filter fun z ↦
    ∃ other ∈ (dwz63PreimageFine K n retained).support,
      other Leg.Z = z.1 ∧
        dwz63PlainCoarseGroup retained
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other ≠ a

theorem mem_dwz63IsolationHoles (K : Type u) [CommRing K]
    (a₀ : retained) {m : ℕ} (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ) (a : retained)
    (z : SegmentedAvailableWord seg alphaTilde) :
    z ∈ dwz63IsolationHoles K retained a₀ seg alphaTilde a ↔
      ∃ other ∈ (dwz63PreimageFine K n retained).support,
        other Leg.Z = z.1 ∧
          dwz63PlainCoarseGroup retained
            (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other ≠ a := by
  classical
  simp [dwz63IsolationHoles]

/-- **The fibre of the grouping**, as a support condition. -/
theorem mem_dwz63PreimageGrouping_fiber_support (K : Type u) [CommRing K] (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _))
    (a : retained)
    (s : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :
    s ∈ ((dwz63PreimageGrouping K a₀ hX hY).fiber a).support ↔
      s ∈ dwz63PreimageZSupport K retained a₀ ∧
        dwz63PlainCoarseGroup retained
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ s = a := by
  classical
  rw [PartitionedTensor.LegGrouping.fiber, PartitionedTensor.withSupport_support,
    PartitionedTensor.LegGrouping.fiberSupport, Finset.mem_filter]
  exact Iff.rfl

/-- **The isolated fibre, selected by the segment types, is the broken localized leaf.**

Left to right the hole-freeness is the fibre's own defining condition; right to left it is where
`Keeps` earns its keep, since a retained `Z`-word is *available*, which is what puts it in range of
`dwz63IsolationHoles`. -/
theorem dwz63PreimageGrouping_fiber_select_eq (K : Type u) [CommRing K] (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _))
    {m : ℕ} (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ) (a : retained) :
    ((dwz63PreimageGrouping K a₀ hX hY).fiber a).select
        ((SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n seg) =
      dwz63BrokenFineLeaf K n m seg alphaTilde
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)
        ((dwz63IsolationHoles K retained a₀ seg alphaTilde a).image Subtype.val) := by
  classical
  set H := (dwz63IsolationHoles K retained a₀ seg alphaTilde a).image Subtype.val with hH
  set grp := dwz63PlainCoarseGroup retained
    (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ with hgrp
  rw [dwz63BrokenFineLeaf_eq_select]
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_select_support, PartitionedTensor.mem_select_support,
      mem_dwz63PreimageGrouping_fiber_support K a₀ hX hY a s,
      mem_dwz63PreimageZSupport K a₀ hX hY s, mem_dwz63PreimageFine_support]
    constructor
    · rintro ⟨⟨⟨⟨hpow, hmem⟩, hpriv⟩, hga⟩, hkeep⟩
      have hcoarse : (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) s :=
        congrArg Subtype.val (hga.symm.trans
          (dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
            (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := s) hX
            (a := (⟨_, hmem⟩ : retained)) rfl))
      have hnot : s Leg.Z ∉ H := by
        intro hmemH
        obtain ⟨z, hz, hzval⟩ := Finset.mem_image.mp hmemH
        obtain ⟨other, hother, hotherZ, hne⟩ :=
          (mem_dwz63IsolationHoles K a₀ seg alphaTilde a z).mp hz
        exact hne ((hpriv other hother (by rw [hotherZ, hzval])).trans hga)
      refine ⟨hpow, fun c ↦ ⟨⟨?_, hkeep c⟩, ?_⟩⟩
      · rw [hcoarse]; rfl
      · exact ((legKeep_iff (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
          Leg.Z (fun z ↦ z ∉ H) s).2 hnot) c
    · rintro ⟨hpow, h⟩
      have hcoarse : coarsenBlockAddress
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) s =
          (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) := by
        funext c
        exact (h c).1.1
      have hmem : coarsenBlockAddress
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) s ∈ retained := by
        rw [hcoarse]; exact a.2
      have hga : grp s = a :=
        dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
          (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := s) hX
          (a := a) ((h Leg.X).1.1).symm
      have hnot : s Leg.Z ∉ H :=
        (legKeep_iff (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
          Leg.Z (fun z ↦ z ∉ H) s).1 fun c ↦ (h c).2
      have havail : ∀ t, segmentMultiplicity seg
          (positiveWordEquiv (PositiveWord CWBlock 1) n (s Leg.Z)) t = alphaTilde t :=
        segmentedKeeps_ofLeg_availability
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) seg alphaTilde (s Leg.Z) (h Leg.Z).1.2
      refine ⟨⟨⟨⟨hpow, hmem⟩, ?_⟩, hga⟩, fun c ↦ (h c).1.2⟩
      intro other hother hotherZ
      rw [← hgrp, hga]
      by_contra hne
      exact hnot (Finset.mem_image.mpr
        ⟨⟨s Leg.Z, havail⟩,
          (mem_dwz63IsolationHoles K a₀ seg alphaTilde a _).mpr
            ⟨other, hother, hotherZ, hne⟩, rfl⟩)
  · rfl

/-! ## Transporting the holes to the reference frame -/

section Reference

variable {m : ℕ}

/-- Availability transports along a position permutation: `seg` moves to `seg ∘ σ`. -/
theorem segmentedAvailable_position_symm (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : PositiveWord (PositiveWord CWBlock 1) n)
    (hw : ∀ t, segmentMultiplicity (seg ∘ ⇑σ)
      (positiveWordEquiv (PositiveWord CWBlock 1) n w) t = alphaTilde t) :
    ∀ t, segmentMultiplicity seg
      (positiveWordEquiv (PositiveWord CWBlock 1) n
        ((positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ).symm w)) t = alphaTilde t := by
  intro t
  rw [positiveWordPositionEquiv_symm, positiveWordEquiv_position_apply,
    segmentMultiplicity_comp_perm_symm]
  exact hw t

/-- The reference-frame hole family: the available reference words whose `σ`-transport the
isolation deletes. -/
noncomputable def dwz63ReferenceHoles (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1))) (a : retained) :
    Finset (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) := by
  classical
  exact Finset.univ.filter fun z ↦
    ∃ other ∈ (dwz63PreimageFine K n retained).support,
      other Leg.Z =
          positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) z.1 ∧
        dwz63PlainCoarseGroup retained
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other ≠ a

/-- **The reference holes transport onto the isolation holes.** -/
theorem dwz63ReferenceHoles_image (K : Type u) [CommRing K] (a₀ : retained)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1))) (a : retained) :
    ((dwz63ReferenceHoles K retained a₀ alphaTilde wRef perm a).image Subtype.val).image
        (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a)) =
      (dwz63IsolationHoles K retained a₀
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
      have h1 : segmentMultiplicity
            (dwz63Seg K n (positiveWordPositionEquiv
              ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef))
            (positiveWordEquiv (PositiveWord CWBlock 1) n
              (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) zw)) t =
          segmentMultiplicity (dwz63Seg K n wRef ∘ ⇑(perm a))
            (positiveWordEquiv (PositiveWord CWBlock 1) n
              (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) zw)) t :=
        congrArg (fun sg ↦ segmentMultiplicity sg
          (positiveWordEquiv (PositiveWord CWBlock 1) n
            (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) zw)) t)
          (dwz63Seg_positionEquiv K n (perm a) wRef)
      rw [h1, positiveWordEquiv_position_apply,
        segmentMultiplicity_comp_perm_general]
      exact hzavail t
    refine Finset.mem_image.mpr ⟨⟨_, havail⟩, ?_, rfl⟩
    refine (mem_dwz63IsolationHoles K a₀ _ alphaTilde a _).mpr ⟨other, hother, ?_, hne⟩
    exact hotherZ
  · intro hw
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hw
    obtain ⟨other, hother, hotherZ, hne⟩ :=
      (mem_dwz63IsolationHoles K a₀ _ alphaTilde a z).mp hz
    obtain ⟨zw, hzavail⟩ := z
    have havail : ∀ t, segmentMultiplicity (dwz63Seg K n wRef)
        (positiveWordEquiv (PositiveWord CWBlock 1) n
          ((positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a)).symm zw)) t =
        alphaTilde t := by
      refine segmentedAvailable_position_symm (dwz63Seg K n wRef) alphaTilde (perm a) zw ?_
      intro t
      have h1 : segmentMultiplicity (dwz63Seg K n wRef ∘ ⇑(perm a))
            (positiveWordEquiv (PositiveWord CWBlock 1) n zw) t =
          segmentMultiplicity (dwz63Seg K n (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef))
            (positiveWordEquiv (PositiveWord CWBlock 1) n zw) t :=
        congrArg (fun sg ↦ segmentMultiplicity sg
          (positiveWordEquiv (PositiveWord CWBlock 1) n zw) t)
          (dwz63Seg_positionEquiv K n (perm a) wRef).symm
      rw [h1]
      exact hzavail t
    refine Finset.mem_image.mpr
      ⟨(positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a)).symm zw, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨⟨_, havail⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨other, hother, by rw [hotherZ, Equiv.apply_symm_apply], hne⟩⟩, rfl⟩
    · rw [Equiv.apply_symm_apply]
      exact hzw

/-- **The grouped fibre reaches the one broken reference leaf.**

Select by the segment types, land on the localized leaf over the triple's own coarse word, then
transport to the reference word --- holes and all. -/
theorem dwz63_preimageFiber_restricts_brokenReferenceLeaf (K : Type u) [CommRing K]
    (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _))
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a : retained,
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a : retained) :
    Restricts ((dwz63PreimageGrouping K a₀ hX hY).fiber a).realize
      (dwz63BrokenFineLeaf K n 15 (dwz63Seg K n wRef) alphaTilde
        (positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)
        ((dwz63ReferenceHoles K retained a₀ alphaTilde wRef perm a).image
          Subtype.val)).realize := by
  classical
  have hsel := Tensor.Restricts.partitionedSelect
    ((dwz63PreimageGrouping K a₀ hX hY).fiber a)
    ((SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n
      (dwz63Seg K n (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef)))
  rw [dwz63PreimageGrouping_fiber_select_eq K a₀ hX hY _ alphaTilde a, ← hperm a] at hsel
  refine hsel.trans (Tensor.Isomorphic.restricts ?_)
  have hiso := dwz63_brokenFineLeaf_isomorphic_position K n alphaTilde wRef (perm a)
    ((dwz63ReferenceHoles K retained a₀ alphaTilde wRef perm a).image Subtype.val)
  rw [dwz63ReferenceHoles_image K a₀ alphaTilde wRef perm a] at hiso
  exact hiso.symm

end Reference

end

end AlgebraicComplexity.Examples
