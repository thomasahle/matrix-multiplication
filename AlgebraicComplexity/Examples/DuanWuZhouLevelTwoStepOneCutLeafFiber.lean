/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutLeafKeep
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGroupedLeaf

set_option autoImplicit false

/-!
# The isolated fibre of `𝒯^{(2)}` is the broken standard-form leaf

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-102`:

> Fixing a triple `(X_I, Y_J, Z_K)`, the structure of `𝒯^{(2)}|_{X_I,Y_J,Z_K}` is as follows.
> Suppose no blocks are zeroed out due to the first rule … In this ideal case
>  `𝒯^* ≝ ⨂_{i+j+k = 2^ℓ} T_{i,j,k}^{⊗ n α(i,j,k)}[splres_{i,j,k}]`.  However, in
> reality, several
> small `Z`-blocks are additionally zeroed out from `𝒯^*` due to the first rule, resulting in
> `𝒯^{(2)}|_{X_I,Y_J,Z_K}` being a broken copy of `𝒯^*` with some holes in its `Z`-variables.
> (`:98-100`)

This module is that sentence over the Step-1 cut: the fibre of image 149's grouping, selected by
the standard-form leaf's own splitting condition, **is** `dwz63BrokenFineLeaf` --- a copy of
`𝒯^*`
with exactly the holes the first rule of Step 2 (`:86`) deletes.

The tree has the same statement on the uncut preimage ambient
(`Examples/DuanWuZhouLevelTwoPreimageLeaf.lean:134`, image 85), which the R1 repair supersedes and
which is neither edited nor imported here.

## What the cut costs, and what pays for it

The `⊆` direction is unchanged: an address of the cut is an address of the uncut ambient, so the
hole-freeness argument is the same.

The `⊇` direction is where the cut has to be re-earned: a leaf address must now be shown to lie in
`𝒯^{(1)}`, i.e. to survive Additional Zeroing-Out Step 1 (`:52-61`).  That is
`dwz63_stepOneKeep_of_leafAvailable` (N4), which reads the paper's own identity at `:70` right to
left.  It is the only new content in the leaf re-issue; everything else is image 85's argument with
the ambient replaced.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:52-61, 70, 84-89, 98-102`, at the section 6.3 instance
(`:332-378`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u

noncomputable section

variable {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- **The `.Y` isolation deletes nothing on the cut ambient.**

Two supported addresses sharing a fine `Y`-word share its coarse image's `Y`-word, and the retained
family is `Y`-injective, so they have the same group.  This is what distinguishes the cut ambient
from a box, where the same isolation is degenerate. -/
theorem dwz63CutYSupport_eq (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _)) :
    dwz63CutYSupport K retained a₀ s = (dwz63FineStepOneCut K n retained a₀ s).support := by
  classical
  refine Finset.Subset.antisymm (groupCompatibilityIsolatedSupport_subset _ _ _ _) ?_
  intro x hx
  rw [dwz63CutYSupport, mem_groupCompatibilityIsolatedSupport]
  refine ⟨hx, ?_⟩
  intro other hother hcompat
  have hx' := ((PartitionedTensor.mem_select_support (dwz63PreimageFine K n retained)
    (dwz63FineStepOneKeep retained a₀ s) x).mp hx).1
  have hother' := ((PartitionedTensor.mem_select_support (dwz63PreimageFine K n retained)
    (dwz63FineStepOneKeep retained a₀ s) other).mp hother).1
  rw [mem_dwz63PreimageFine_support] at hx' hother'
  have hsg := dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
    (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := x) hX
    (a := (⟨_, hx'.2⟩ : retained)) rfl
  have hog := dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
    (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := other) hX
    (a := (⟨_, hother'.2⟩ : retained)) rfl
  rw [hsg, hog]
  refine Subtype.ext (hY (Finset.mem_coe.mpr hother'.2) (Finset.mem_coe.mpr hx'.2) ?_)
  show positiveWordMap (cwSquareDegreeMap Leg.Y) n (other Leg.Y) =
    positiveWordMap (cwSquareDegreeMap Leg.Y) n (x Leg.Y)
  rw [hcompat]

/-- **What the `.Z` isolation keeps** (`global_value.tex:86`): the addresses whose fine `Z`-word no
competing group carries. -/
theorem mem_dwz63CutZSupport (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _))
    (x : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :
    x ∈ dwz63CutZSupport K retained a₀ s ↔
      x ∈ (dwz63FineStepOneCut K n retained a₀ s).support ∧
        ∀ other ∈ (dwz63FineStepOneCut K n retained a₀ s).support,
          other Leg.Z = x Leg.Z →
            dwz63PlainCoarseGroup retained
                (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other =
              dwz63PlainCoarseGroup retained
                (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ x := by
  rw [dwz63CutZSupport, dwz63CutYSupport_eq K a₀ s hX hY,
    mem_groupCompatibilityIsolatedSupport]
  exact Iff.rfl

/-- **The holes of Step 2 on `𝒯^{(1)}`** (`global_value.tex:86`, `:100`): the available `Z`-words
carried by a group other than `a`.  The reference-frame twin is image 145's
`dwz63CutReferenceHoles`. -/
def dwz63CutIsolationHoles (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) (s : ℕ) {m : ℕ} (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ) (a : retained) :
    Finset (SegmentedAvailableWord seg alphaTilde) := by
  classical
  exact Finset.univ.filter fun z ↦
    ∃ other ∈ (dwz63FineStepOneCut K n retained a₀ s).support,
      other Leg.Z = z.1 ∧
        dwz63PlainCoarseGroup retained
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other ≠ a

@[simp] theorem mem_dwz63CutIsolationHoles (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    {m : ℕ} (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ) (a : retained)
    (z : SegmentedAvailableWord seg alphaTilde) :
    z ∈ dwz63CutIsolationHoles K retained a₀ s seg alphaTilde a ↔
      ∃ other ∈ (dwz63FineStepOneCut K n retained a₀ s).support,
        other Leg.Z = z.1 ∧
          dwz63PlainCoarseGroup retained
            (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other ≠ a := by
  classical
  simp [dwz63CutIsolationHoles]

/-- **The fibre of the grouping**, as a support condition (`global_value.tex:89`). -/
theorem mem_dwz63CutGrouping_fiber_support (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _))
    (a : retained)
    (x : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :
    x ∈ ((dwz63CutGrouping K a₀ s hX hY).fiber a).support ↔
      x ∈ dwz63CutZSupport K retained a₀ s ∧
        dwz63PlainCoarseGroup retained
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ x = a := by
  classical
  rw [PartitionedTensor.LegGrouping.fiber, PartitionedTensor.withSupport_support,
    PartitionedTensor.LegGrouping.fiberSupport, Finset.mem_filter]
  exact Iff.rfl

/-- **The isolated fibre, selected by the segment types, is the broken standard-form leaf**
(`global_value.tex:98-100`).

`⊆` is the fibre's own hole-freeness, unchanged from the uncut argument.  `⊇` is where the
Step-1
cut is re-earned: a leaf address is *available*, and an available address over a retained triple
survives Step 1 by `dwz63_stepOneKeep_of_leafAvailable` (N4), the paper's `:70` identity read right
to left.

Proof sketch: unfold both sides by `mem_select_support`; left to right, read the group off the
`X`-leg (`dwz63PlainCoarseGroup_eq_of_x`) and turn the fibre's privacy condition into
hole-freeness; right to left, recover the coarse condition, the group, availability
(`segmentedKeeps_ofLeg_availability`), and then the Step-1 keep from N4, and conclude by
contradiction against hole-freeness. -/
theorem dwz63CutGrouping_fiber_select_eq (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _))
    {alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ}
    (hS : (dwz63SplitPair s).splitCount = alphaTilde) (a : retained)
    (seg : Fin (n + 1) → Fin 15)
    (hseg : seg =
      dwz63CellWordOfAddress (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) :
    ((dwz63CutGrouping K a₀ s hX hY).fiber a).select
        ((SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n seg) =
      dwz63BrokenFineLeaf K n 15 seg alphaTilde
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)
        ((dwz63CutIsolationHoles K retained a₀ s seg alphaTilde a).image Subtype.val) := by
  classical
  set H := (dwz63CutIsolationHoles K retained a₀ s seg alphaTilde a).image Subtype.val with hH
  set grp := dwz63PlainCoarseGroup retained
    (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ with hgrp
  rw [dwz63BrokenFineLeaf_eq_select]
  apply PartitionedTensor.ext
  · ext x
    rw [PartitionedTensor.mem_select_support, PartitionedTensor.mem_select_support,
      mem_dwz63CutGrouping_fiber_support K a₀ s hX hY a x,
      mem_dwz63CutZSupport K a₀ s hX hY x]
    constructor
    · rintro ⟨⟨⟨hcut, hpriv⟩, hga⟩, hkeep⟩
      have hpre := ((PartitionedTensor.mem_select_support (dwz63PreimageFine K n retained)
        (dwz63FineStepOneKeep retained a₀ s) x).mp hcut).1
      obtain ⟨hpow, hmem⟩ := (mem_dwz63PreimageFine_support K n retained x).mp hpre
      have hcoarse : (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) x :=
        congrArg Subtype.val (hga.symm.trans
          (dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
            (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := x) hX
            (a := (⟨_, hmem⟩ : retained)) rfl))
      have hnot : x Leg.Z ∉ H := by
        intro hmemH
        obtain ⟨z, hz, hzval⟩ := Finset.mem_image.mp hmemH
        obtain ⟨other, hother, hotherZ, hne⟩ :=
          (mem_dwz63CutIsolationHoles K a₀ s seg alphaTilde a z).mp hz
        exact hne ((hpriv other hother (by rw [hotherZ, hzval])).trans hga)
      refine ⟨hpow, fun c ↦ ⟨⟨?_, hkeep c⟩, ?_⟩⟩
      · rw [hcoarse]; rfl
      · exact ((legKeep_iff (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
          Leg.Z (fun z ↦ z ∉ H) x).2 hnot) c
    · rintro ⟨hpow, h⟩
      have hcoarse : coarsenBlockAddress
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) x =
          (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) := by
        funext c
        exact (h c).1.1
      have hmem : coarsenBlockAddress
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) x ∈ retained := by
        rw [hcoarse]; exact a.2
      have hga : grp x = a :=
        dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
          (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := x) hX
          (a := a) ((h Leg.X).1.1).symm
      have hnot : x Leg.Z ∉ H :=
        (legKeep_iff (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
          Leg.Z (fun z ↦ z ∉ H) x).1 fun c ↦ (h c).2
      have havail : ∀ t, segmentMultiplicity seg
          (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Z)) t = alphaTilde t :=
        segmentedKeeps_ofLeg_availability
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) seg alphaTilde (x Leg.Z) (h Leg.Z).1.2
      -- N4: the leaf's own address survives Additional Zeroing-Out Step 1 (`:52-61`, via `:70`)
      have hstep : ∀ c, dwz63FineStepOneKeep retained a₀ s c (x c) :=
        dwz63_stepOneKeep_of_leafAvailable K a₀ s hX hY hS a x hpow hcoarse
          (by rw [← hseg]; exact havail)
      have hcut : x ∈ (dwz63FineStepOneCut K n retained a₀ s).support :=
        (PartitionedTensor.mem_select_support (dwz63PreimageFine K n retained)
          (dwz63FineStepOneKeep retained a₀ s) x).mpr
          ⟨(mem_dwz63PreimageFine_support K n retained x).mpr ⟨hpow, hmem⟩, hstep⟩
      refine ⟨⟨⟨hcut, ?_⟩, hga⟩, fun c ↦ (h c).1.2⟩
      intro other hother hotherZ
      rw [← hgrp, hga]
      by_contra hne
      exact hnot (Finset.mem_image.mpr
        ⟨⟨x Leg.Z, havail⟩,
          (mem_dwz63CutIsolationHoles K a₀ s seg alphaTilde a _).mpr
            ⟨other, hother, hotherZ, hne⟩, rfl⟩)
  · rfl

end

end AlgebraicComplexity.Examples
