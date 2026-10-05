/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLocalizedStage

set_option autoImplicit false

/-!
# The grouped `hleaf`, proved

`Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s
`dwz63_localizedGroupedStage_of_segmentedRepair` carries `hleaf` as a hypothesis because image
57's `fine` is abstract: a broken group is a sub-partition of `fine`, so nothing can be said about
it until `fine` is pinned.  This module pins it and discharges `hleaf`.

`dwz63PlainFine` is the depth-one fine power cut to the addresses that lie over a retained coarse
triple on **all three legs** and avoid that triple's holes.  Both grouped premises then hold by
construction (`dwz63PlainFine_hcover`, `dwz63PlainFine_hambient`), and the support of a broken
group collapses to exactly one coarse fiber intersected with the hole-free part
(`mem_dwz63PlainBrokenGroup_dwz63PlainFine`) --- Step 2 removes nothing further, because a
hole-free address is already privately compatible.

From there `hleaf` is the chain the lane already owns: a legwise `select` by the segment types
lands on the localized leaf over that triple's own coarse word, and the uniformity isomorphism
carries it to the reference word.  The one new ingredient is that the isomorphism must move the
holes too, so the fine hole set is *defined* as the position-transport of the reference one
(`dwz63TransportedHoles`); the reference-frame hole set, which is what `hbudget` counts, is
unchanged.

`[DuanWuZhou2022]`, section 6.3, `global_value.tex`, `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

noncomputable section

/-! ## Two selection identities -/

section SelectApi

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Two successive selections are one selection by the legwise conjunction.  The committed
`select_select_legKeep` is the case where both are leg-local. -/
theorem partitionedSelect_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep₁ keep₂ : ∀ c, A c → Prop)
    [∀ c a, Decidable (keep₁ c a)] [∀ c a, Decidable (keep₂ c a)] :
    (P.select keep₁).select keep₂ = P.select (fun c a ↦ keep₁ c a ∧ keep₂ c a) := by
  classical
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_select_support, PartitionedTensor.mem_select_support,
      PartitionedTensor.mem_select_support]
    constructor
    · rintro ⟨⟨hs, h₁⟩, h₂⟩
      exact ⟨hs, fun c ↦ ⟨h₁ c, h₂ c⟩⟩
    · rintro ⟨hs, h⟩
      exact ⟨⟨hs, fun c ↦ (h c).1⟩, fun c ↦ (h c).2⟩
  · rfl

/-- Selections by pointwise equivalent predicates agree. -/
theorem partitionedSelect_congr
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep₁ keep₂ : ∀ c, A c → Prop)
    [∀ c a, Decidable (keep₁ c a)] [∀ c a, Decidable (keep₂ c a)]
    (h : ∀ c a, keep₁ c a ↔ keep₂ c a) :
    P.select keep₁ = P.select keep₂ := by
  classical
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_select_support, PartitionedTensor.mem_select_support]
    exact and_congr_right fun _ ↦ forall_congr' fun c ↦ h c (s c)
  · rfl

end SelectApi

/-! ## The broken leaf at a plain hole set -/

/-- The localized segmented leaf with a plain finite set of `Z`-words destroyed.  Definitionally
`dwz63BrokenSegmentedFineFiber` at `H = holes.image Subtype.val`. -/
noncomputable def dwz63BrokenFineLeaf (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n)) :=
  (dwz63SegmentedFineFiber K n m seg alphaTilde target).holeSelect Leg.Z fun z ↦ z ∈ H

theorem dwz63BrokenSegmentedFineFiber_eq_brokenFineLeaf (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (holes : Finset (SegmentedAvailableWord seg alphaTilde)) :
    dwz63BrokenSegmentedFineFiber K n m seg alphaTilde target holes =
      dwz63BrokenFineLeaf K n m seg alphaTilde target (holes.image Subtype.val) := rfl

/-- The legwise keep predicate of the broken leaf: over the target, segment-typed, hole-free. -/
def dwz63BrokenLeafKeep (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    ∀ c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop :=
  fun c w ↦ segmentedLocalizedKeep cwSquareDegreeMap seg
      (SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde) target c w ∧
    legKeep (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
      Leg.Z (fun z ↦ z ∉ H) c w

noncomputable instance dwz63BrokenLeafKeepDecidable (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n))
    (c : Leg) (w : PositiveWord (PositiveWord CWBlock 1) n) :
    Decidable (dwz63BrokenLeafKeep n m seg alphaTilde target H c w) :=
  Classical.dec _

/-- The broken leaf as a single selection of the ambient fine power. -/
theorem dwz63BrokenFineLeaf_eq_select (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    dwz63BrokenFineLeaf K n m seg alphaTilde target H =
      (((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).select
        (dwz63BrokenLeafKeep n m seg alphaTilde target H) := by
  classical
  apply PartitionedTensor.ext
  · ext s
    rw [dwz63BrokenFineLeaf, PartitionedTensor.mem_holeSelect_support,
      dwz63SegmentedFineFiber, PartitionedTensor.segmentedLocalizedSplittingPower,
      PartitionedTensor.mem_select_support, PartitionedTensor.mem_select_support]
    constructor
    · rintro ⟨⟨hs, hkeep⟩, hhole⟩
      exact ⟨hs, fun c ↦ ⟨hkeep c,
        ((legKeep_iff (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
          Leg.Z (fun z ↦ z ∉ H) s).2 hhole) c⟩⟩
    · rintro ⟨hs, h⟩
      exact ⟨⟨hs, fun c ↦ (h c).1⟩,
        (legKeep_iff (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
          Leg.Z (fun z ↦ z ∉ H) s).1 fun c ↦ (h c).2⟩
  · rfl

/-! ## Moving a broken leaf between coarse words -/

/-- The fiber-level keep predicate of the broken leaf. -/
def dwz63FiberBrokenKeep (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    ∀ c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop :=
  fun c w ↦ (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n seg c w ∧
    legKeep (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
      Leg.Z (fun z ↦ z ∉ H) c w

noncomputable instance dwz63FiberBrokenKeepDecidable (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n))
    (c : Leg) (w : PositiveWord (PositiveWord CWBlock 1) n) :
    Decidable (dwz63FiberBrokenKeep n m seg alphaTilde H c w) :=
  Classical.dec _

/-- The broken leaf in fiber-then-select form. -/
theorem dwz63BrokenFineLeaf_eq_fiberSelect (K : Type u) [CommRing K] (n m : ℕ)
    (seg : Fin (n + 1) → Fin m)
    (alphaTilde : Fin m → PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    ((((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) target).select
      (dwz63FiberBrokenKeep n m seg alphaTilde H) =
      dwz63BrokenFineLeaf K n m seg alphaTilde target H := by
  classical
  rw [PartitionedTensor.coarseningFiber_select_eq_select, dwz63BrokenFineLeaf_eq_select]
  refine partitionedSelect_congr _ _ _ fun c w ↦ ?_
  constructor
  · rintro ⟨hf, hk, hl⟩
    exact ⟨⟨hf, hk⟩, hl⟩
  · rintro ⟨⟨hf, hk⟩, hl⟩
    exact ⟨hf, hk, hl⟩

/-- **The broken leaf moves with the coarse word.**

`dwz63_segmentedFineFiber_isomorphic_position` with the hashing damage carried along: a position
permutation transports the coarse target, the segmentation *and* the hole set, all by the same
`σ`.  This is what lets one reference hole set serve every retained triple. -/
theorem dwz63_brokenFineLeaf_isomorphic_position (K : Type u) [CommRing K] (n : ℕ)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (σ : Equiv.Perm (Fin (n + 1)))
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    Isomorphic
      (dwz63BrokenFineLeaf K n 15 (dwz63Seg K n wRef) alphaTilde
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) H).realize
      (dwz63BrokenFineLeaf K n 15
        (dwz63Seg K n (positiveWordPositionEquiv
          ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef)) alphaTilde
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef))
        (H.image (positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ))).realize := by
  classical
  have hmem : ∀ w : PositiveWord (PositiveWord CWBlock 1) n,
      ((positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ).symm w ∈ H) ↔
        w ∈ H.image (positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ) := by
    intro w
    rw [Finset.mem_image]
    constructor
    · intro h
      exact ⟨_, h, Equiv.apply_symm_apply _ _⟩
    · rintro ⟨x, hx, rfl⟩
      rwa [Equiv.symm_apply_apply]
  have hkeep : ∀ (c : Leg) (w : PositiveWord (PositiveWord CWBlock 1) n),
      dwz63FiberBrokenKeep n 15 (dwz63Seg K n wRef) alphaTilde H c
          ((positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ).symm w) ↔
        dwz63FiberBrokenKeep n 15 (dwz63Seg K n wRef ∘ ⇑σ) alphaTilde
          (H.image (positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ)) c w := by
    intro c w
    refine and_congr
      (SegmentedSplitRestriction.keeps_comp_perm
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde)
        n (dwz63Seg K n wRef) σ c w) ?_
    cases c <;> simp [legKeep, hmem w]
  rw [← dwz63BrokenFineLeaf_eq_fiberSelect, ← dwz63BrokenFineLeaf_eq_fiberSelect,
    dwz63Seg_positionEquiv K n σ wRef,
    ← positionRelabelBlockAddress_positiveSupportWordBlockAddress]
  exact Tensor.Isomorphic.positivePower_localizedCoarseningFiberSelect_position_two
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)
    (dwz63FiberBrokenKeep n 15 (dwz63Seg K n wRef) alphaTilde H)
    (dwz63FiberBrokenKeep n 15 (dwz63Seg K n wRef ∘ ⇑σ) alphaTilde
      (H.image (positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ)))
    σ hkeep

/-! ## The DWZ fine partition -/

section Fine

variable {K : Type u} [CommRing K] {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- The coarsening reader of the plain route: coarsen each fine leg word letterwise. -/
def dwz63FineCoarse (n : ℕ) :
    ∀ c : Leg, PositiveWord (PositiveWord CWBlock 1) n → PositiveWord (Fin 5) n :=
  fun c ↦ positiveWordMap (cwSquareDegreeMap c) n

/-- **The DWZ fine partition**: the depth-one fine power cut to the addresses lying over a
retained coarse triple on all three legs and free of that triple's holes.  Both premises of image
57's grouped opening hold for it by construction. -/
noncomputable def dwz63PlainFine (K : Type u) [CommRing K] (n : ℕ)
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained)
    (holesFine : retained → Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    PartitionedTensor (K := K)
      (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
      (PositivePowerBlockSpace K
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n) := by
  classical
  exact (((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).withSupport
    ((((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).support.filter
      fun s ↦ (∀ c, ((dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀ s :
            BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) c =
          dwz63FineCoarse n c (s c)) ∧
        s .Z ∉ holesFine (dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀ s))

theorem mem_dwz63PlainFine_support (a₀ : retained)
    (holesFine : retained → Finset (PositiveWord (PositiveWord CWBlock 1) n))
    (s : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :
    s ∈ (dwz63PlainFine K n retained a₀ holesFine).support ↔
      s ∈ (((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).support ∧
        (∀ c, ((dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀ s :
            BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) c =
          dwz63FineCoarse n c (s c)) ∧
        s .Z ∉ holesFine (dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀ s) := by
  classical
  rw [dwz63PlainFine, PartitionedTensor.withSupport_support, Finset.mem_filter]

/-- The `hcover` premise, by construction. -/
theorem dwz63PlainFine_hcover (a₀ : retained)
    (holesFine : retained → Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    ∀ s ∈ (dwz63PlainFine K n retained a₀ holesFine).support, ∃ a : retained,
      ∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c =
        dwz63FineCoarse n c (s c) := by
  intro s hs
  rw [mem_dwz63PlainFine_support] at hs
  exact ⟨_, hs.2.1⟩

/-- The `hambient` premise, by construction. -/
theorem dwz63PlainFine_hambient (a₀ : retained)
    (holesFine : retained → Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    ∀ s ∈ (dwz63PlainFine K n retained a₀ holesFine).support,
      s .Z ∉ holesFine (dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀ s) := by
  intro s hs
  rw [mem_dwz63PlainFine_support] at hs
  exact hs.2.2

/-- **The support of a broken group is one coarse fiber, hole-free.**

Step 2 removes nothing further: a hole-free address is privately compatible already, so the
grouped `Z`-isolation keeps the whole ambient. -/
theorem mem_dwz63PlainBrokenGroup_dwz63PlainFine (a₀ : retained)
    (holesFine : retained → Finset (PositiveWord (PositiveWord CWBlock 1) n))
    {compatibleWith usefulFor :
      PositiveWord (PositiveWord CWBlock 1) n → retained → Prop}
    (hrefines : ∀ z a, usefulFor z a → compatibleWith z a)
    (hholes : ∀ (a : retained) (z : PositiveWord (PositiveWord CWBlock 1) n),
      z ∉ holesFine a → usefulFor z a ∧ ∀ b, b ≠ a → ¬ compatibleWith z b)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (a : retained)
    (s : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :
    s ∈ (dwz63PlainBrokenGroup (dwz63PlainFine K n retained a₀ holesFine)
        (dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀) usefulFor a).support ↔
      s ∈ (((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).support ∧
        (∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c =
          dwz63FineCoarse n c (s c)) ∧ s .Z ∉ holesFine a := by
  classical
  rw [dwz63PlainBrokenGroup, PartitionedTensor.withSupport_support, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hga⟩
    have hs : s ∈ (dwz63PlainFine K n retained a₀ holesFine).support :=
      groupCompatibilityIsolatedSupport_subset _ _ _ _ hz
    rw [mem_dwz63PlainFine_support] at hs
    exact ⟨hs.1, hga ▸ hs.2.1, hga ▸ hs.2.2⟩
  · rintro ⟨hpow, hcoarse, hhole⟩
    have hga : dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀ s = a :=
      dwz63PlainCoarseGroup_eq_of_x hX (hcoarse .X)
    have hs : s ∈ (dwz63PlainFine K n retained a₀ holesFine).support := by
      rw [mem_dwz63PlainFine_support, hga]
      exact ⟨hpow, hcoarse, hhole⟩
    exact ⟨dwz63_mem_plainGroupedZSupport_of_notMem_holes hrefines hholes hs
      (by rw [hga]; exact hhole), hga⟩

end Fine

/-! ## `hleaf`, proved -/

section Leaf

variable {K : Type u} [CommRing K] {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- The fine hole set of a retained triple: the reference hole set, transported to that triple's
frame by the permutation carrying the reference coarse word to its own. -/
noncomputable def dwz63TransportedHoles (n : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (H : Finset (PositiveWord (PositiveWord CWBlock 1) n)) :
    Finset (PositiveWord (PositiveWord CWBlock 1) n) :=
  H.image (positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ)

/-- **A broken group is the localized leaf over its own coarse word, once the segment types are
selected.** -/
theorem dwz63PlainBrokenGroup_select_eq_brokenFineLeaf (a₀ : retained)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (holesFine : retained → Finset (PositiveWord (PositiveWord CWBlock 1) n))
    {compatibleWith usefulFor :
      PositiveWord (PositiveWord CWBlock 1) n → retained → Prop}
    (hrefines : ∀ z a, usefulFor z a → compatibleWith z a)
    (hholes : ∀ (a : retained) (z : PositiveWord (PositiveWord CWBlock 1) n),
      z ∉ holesFine a → usefulFor z a ∧ ∀ b, b ≠ a → ¬ compatibleWith z b)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (a : retained) (seg : Fin (n + 1) → Fin 15) :
    ((dwz63PlainBrokenGroup (dwz63PlainFine K n retained a₀ holesFine)
        (dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀) usefulFor a).select
      ((SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n seg)) =
      dwz63BrokenFineLeaf K n 15 seg alphaTilde
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) (holesFine a) := by
  classical
  rw [dwz63BrokenFineLeaf_eq_select]
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_select_support, PartitionedTensor.mem_select_support,
      mem_dwz63PlainBrokenGroup_dwz63PlainFine a₀ holesFine hrefines hholes hX a s]
    constructor
    · rintro ⟨⟨hpow, hcoarse, hhole⟩, hkeep⟩
      refine ⟨hpow, fun c ↦ ⟨⟨(hcoarse c).symm, hkeep c⟩, ?_⟩⟩
      exact ((legKeep_iff (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
        Leg.Z (fun z ↦ z ∉ holesFine a) s).2 hhole) c
    · rintro ⟨hpow, h⟩
      exact ⟨⟨hpow, fun c ↦ ((h c).1.1).symm,
        (legKeep_iff (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
          Leg.Z (fun z ↦ z ∉ holesFine a) s).1 fun c ↦ (h c).2⟩,
        fun c ↦ (h c).1.2⟩
  · rfl

/-- **The grouped `hleaf`, proved.**

Every broken group restricts onto the one broken reference leaf: a legwise selection by the
segment types lands on the localized leaf over that triple's own coarse word, and
`dwz63_brokenFineLeaf_isomorphic_position` carries it, holes and all, to the reference word. -/
theorem dwz63_brokenGroup_restricts_brokenReferenceLeaf (a₀ : retained)
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a : retained,
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (Href : retained → Finset (PositiveWord (PositiveWord CWBlock 1) n))
    {compatibleWith usefulFor :
      PositiveWord (PositiveWord CWBlock 1) n → retained → Prop}
    (hrefines : ∀ z a, usefulFor z a → compatibleWith z a)
    (hholes : ∀ (a : retained) (z : PositiveWord (PositiveWord CWBlock 1) n),
      z ∉ dwz63TransportedHoles n (perm a) (Href a) →
        usefulFor z a ∧ ∀ b, b ≠ a → ¬ compatibleWith z b)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (a : retained) :
    Restricts
      (dwz63PlainBrokenGroup
        (dwz63PlainFine K n retained a₀ fun b ↦ dwz63TransportedHoles n (perm b) (Href b))
        (dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀) usefulFor a).realize
      (dwz63BrokenFineLeaf K n 15 (dwz63Seg K n wRef) alphaTilde
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) (Href a)).realize := by
  classical
  have hselect := Tensor.Restricts.partitionedSelect
    (dwz63PlainBrokenGroup
      (dwz63PlainFine K n retained a₀ fun b ↦ dwz63TransportedHoles n (perm b) (Href b))
      (dwz63PlainCoarseGroup retained (dwz63FineCoarse n) a₀) usefulFor a)
    ((SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z alphaTilde).Keeps n
      (dwz63Seg K n (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef)))
  rw [dwz63PlainBrokenGroup_select_eq_brokenFineLeaf a₀ alphaTilde
    (fun b ↦ dwz63TransportedHoles n (perm b) (Href b)) hrefines hholes hX a,
    ← hperm a] at hselect
  exact hselect.trans (Tensor.Isomorphic.restricts
    (dwz63_brokenFineLeaf_isomorphic_position K n alphaTilde wRef (perm a) (Href a)).symm)

end Leaf

/-! ## The stage with `hleaf` discharged -/

section Stage

variable {R : Type v} [Field R]

/-- **The section 6.3 plain stage, with `hclaim3` the only mathematical hypothesis.**

`Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s stage with `hleaf`, `hcover` and `hambient`
all discharged: `fine` is `dwz63PlainFine`, so the two grouped premises hold by construction and
`hleaf` is `dwz63_brokenGroup_restricts_brokenReferenceLeaf`.

The fine hole family is `dwz63TransportedHoles`, *not* the reference family: the uniformity
isomorphism moves holes along with words, so each retained triple is damaged in its own frame
while the budget still counts the reference frame.  That decoupling is why this is a new theorem
rather than an instantiation of the frozen stage, whose `hholes`/`hambient` binders are pinned to
the reference family. -/
theorem dwz63_groupedStage_of_claim3 [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R))) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hclaim3 : SegmentedFiberIndependence (dwz63Seg K n wRef) alphaTilde)
    (a₀ : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
    (perm : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) →
      Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed),
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv
            ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (holes : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) →
      Finset (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde))
    {compatibleWith usefulFor :
      PositiveWord (PositiveWord CWBlock 1) n →
        (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) → Prop}
    (hrefines : ∀ z a, usefulFor z a → compatibleWith z a)
    (hholes : ∀ (a : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed))
        (z : PositiveWord (PositiveWord CWBlock 1) n),
      z ∉ dwz63TransportedHoles n (perm a) ((holes a).image Subtype.val) →
        usefulFor z a ∧ ∀ b, b ≠ a → ¬ compatibleWith z b)
    (hfine : Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (dwz63PlainFine K n (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) a₀
        (fun b ↦ dwz63TransportedHoles n (perm b) ((holes b).image Subtype.val))).realize)
    {β : Type} [Fintype β] [DecidableEq β]
    (batch : (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) → β)
    (hbatch : Function.Surjective batch)
    (hbudget : ∀ b : β,
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) *
          ∏ a : {a // batch a = b}, (holes a.1).card <
        Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) ^
          Fintype.card {a // batch a = b}) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K
          (PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n))
        fun _ ↦ (dwz63ReferenceLeaf K n alphaTilde wRef).realize) := by
  classical
  have hX := dwz63_x_injOn_plainJointRetained K hinj n t markedWords hmarked B hB seed
  refine (dwz63_plainGroupedStage_of_brokenLeaf
    (dwz63PlainFine K n (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed) a₀
      (fun b ↦ dwz63TransportedHoles n (perm b) ((holes b).image Subtype.val)))
    hfine (dwz63FineCoarse n) a₀ hX
    ((cwSquarePartitionHashEncoding hinj).y_injectiveOn_markedXYIsolatedPowerAddresses
      n (dwz63PlainMarginalWords K n t) markedWords hmarked B hB seed)
    (dwz63PlainFine_hcover a₀ _)
    (compatibleWith := compatibleWith) hholes (dwz63PlainFine_hambient a₀ _)
    (fun a ↦ dwz63BrokenSegmentedFineFiber K n 15 (dwz63Seg K n wRef) alphaTilde
      (positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) n wRef) (holes a))
    (fun a ↦ dwz63_brokenGroup_restricts_brokenReferenceLeaf a₀ alphaTilde wRef perm hperm
      (fun b ↦ (holes b).image Subtype.val) hrefines hholes hX a)).trans ?_
  simp only [dwz63ReferenceLeaf, dwz63BrokenSegmentedFineFiber, dwz63SegmentedFineFiber]
  exact restricts_indexedDirectSum_segmentedLocalizedHoleRepair_batched
    ((cwPartitionedTensor K dwz63Q).positivePower 1) cwSquareDegreeMap n 15
    (dwz63Seg K n wRef) alphaTilde hclaim3
    (positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n wRef)
    (fun σ hperm' ↦ dwz63_positionRelabel_target_eq K n σ wRef hperm')
    batch hbatch holes hbudget

end Stage

end

end AlgebraicComplexity.Examples
