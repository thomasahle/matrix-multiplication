/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.CompatibilityZeroing
import AlgebraicComplexity.Tensor.PartitionedGrouping

/-!
# Compatibility zeroing modulo a coarse constituent group

The compatibility cleanup in recursive laser arguments does not make each fine block label
belong to a unique fine monomial.  It makes it belong to a unique coarse constituent.  This file
formalizes that distinction.

An address grouping is leg-readable when equal fine labels force equal groups.  A grouped
compatibility zero-out deletes a label only when it is compatible with addresses in different
groups.  The survivors remain an exact variable restriction and acquire a leg-local group
reader.  Once all three legs have such readers, `PartitionedTensor.LegGrouping` assembles the
fine constituents into an indexed direct sum of coarse-group fibers.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {Γ : Type x}

/-- Every selected fine address lies in the ambient support, and its coarse group is determined
by its label on `pivot`.  Fine addresses sharing a label may remain distinct. -/
def HasGroupUniqueLegFibers (ambient selected : Finset (BlockAddress A))
    (group : BlockAddress A → Γ) (pivot : Leg) : Prop :=
  selected ⊆ ambient ∧
    ∀ s ∈ selected, ∀ t ∈ ambient, t pivot = s pivot → group t = group s

/-- A selected family is saturated by coarse groups inside an ambient support: retaining one
fine address retains every ambient fine address in the same coarse group. -/
def IsGroupSaturatedIn (ambient selected : Finset (BlockAddress A))
    (group : BlockAddress A → Γ) : Prop :=
  ∀ s ∈ selected, ∀ t ∈ ambient, group t = group s → t ∈ selected

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- If the pivot label determines the coarse group on the selected family and selection keeps
whole coarse groups, then selection is an honest pivot-variable zero-out. -/
theorem HasGroupUniqueLegFibers.isProjectionClosed_of_groupSaturated
    {ambient selected : Finset (BlockAddress A)} {group : BlockAddress A → Γ}
    {pivot : Leg} (hunique : HasGroupUniqueLegFibers ambient selected group pivot)
    (hsaturated : IsGroupSaturatedIn ambient selected group) :
    IsProjectionClosed ambient selected {pivot} := by
  refine ⟨hunique.1, ?_⟩
  intro address haddress hprojected
  obtain ⟨witness, hwitness, hlabel⟩ := hprojected pivot (by simp)
  exact hsaturated witness hwitness address haddress
    (hunique.2 witness hwitness address haddress hlabel)

namespace Restricts

/-- Exact variable restriction for a coarse-group-saturated selected support. -/
theorem partitionedGroupSaturated
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (hunique : HasGroupUniqueLegFibers P.support selected group pivot)
    (hsaturated : IsGroupSaturatedIn P.support selected group) :
    Restricts P.realize (P.withSupport selected).realize :=
  partitionedProjectionClosed P selected {pivot}
    (hunique.isProjectionClosed_of_groupSaturated hsaturated)

end Restricts

/-- A fine address survives grouped compatibility isolation when every ambient address compatible
with its used label belongs to the same coarse group. -/
def IsGroupUniquelyCompatible (ambient : Finset (BlockAddress A))
    (group : BlockAddress A → Γ) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) (address : BlockAddress A) : Prop :=
  address ∈ ambient ∧
    ∀ other ∈ ambient, compatible (address pivot) other →
      group other = group address

/-- Delete precisely the labels compatible with addresses in more than one coarse group. -/
noncomputable def groupCompatibilityIsolatedSupport
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) : Finset (BlockAddress A) := by
  classical
  exact ambient.filter (IsGroupUniquelyCompatible ambient group pivot compatible)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem mem_groupCompatibilityIsolatedSupport
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) (address : BlockAddress A) :
    address ∈ groupCompatibilityIsolatedSupport ambient group pivot compatible ↔
      IsGroupUniquelyCompatible ambient group pivot compatible address := by
  classical
  simp [groupCompatibilityIsolatedSupport, IsGroupUniquelyCompatible]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem groupCompatibilityIsolatedSupport_subset
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) :
    groupCompatibilityIsolatedSupport ambient group pivot compatible ⊆ ambient := by
  intro address haddress
  exact (mem_groupCompatibilityIsolatedSupport
    ambient group pivot compatible address).mp haddress |>.1

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Sound grouped compatibility isolation makes the coarse group readable from the pivot label. -/
theorem groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound ambient pivot compatible) :
    HasGroupUniqueLegFibers ambient
      (groupCompatibilityIsolatedSupport ambient group pivot compatible) group pivot := by
  refine ⟨groupCompatibilityIsolatedSupport_subset ambient group pivot compatible, ?_⟩
  intro selected hselected other hother hlabel
  have hunique := (mem_groupCompatibilityIsolatedSupport
    ambient group pivot compatible selected).mp hselected |>.2
  apply hunique other hother
  have hcompatible := hsound other hother
  simpa only [hlabel] using hcompatible

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Grouped compatibility isolation is closed under the actual pivot-label projection, hence is
implemented by a genuine variable zero-out. -/
theorem groupCompatibilityIsolatedSupport_isProjectionClosed
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound ambient pivot compatible) :
    IsProjectionClosed ambient
      (groupCompatibilityIsolatedSupport ambient group pivot compatible) {pivot} := by
  let selected := groupCompatibilityIsolatedSupport ambient group pivot compatible
  have hgroup : HasGroupUniqueLegFibers ambient selected group pivot :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      ambient group pivot compatible hsound
  refine ⟨hgroup.1, ?_⟩
  intro address haddress hprojected
  obtain ⟨witness, hwitness, hlabel⟩ := hprojected pivot (by simp)
  apply (mem_groupCompatibilityIsolatedSupport
    ambient group pivot compatible address).mpr
  refine ⟨haddress, ?_⟩
  have haddressGroup : group address = group witness :=
    hgroup.2 witness hwitness address haddress hlabel
  have hwitnessUnique := (mem_groupCompatibilityIsolatedSupport
    ambient group pivot compatible witness).mp hwitness |>.2
  intro other hother hcompatible
  have hotherGroup : group other = group witness := by
    apply hwitnessUnique other hother
    rw [← hlabel]
    exact hcompatible
  exact hotherGroup.trans haddressGroup.symm

namespace Restricts

/-- Exact tensor restriction implementing compatibility zero-out modulo coarse groups. -/
theorem partitionedGroupCompatibilityIsolated
    (P : PartitionedTensor (K := K) (A := A) V) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound P.support pivot compatible) :
    Restricts P.realize
      (P.withSupport
        (groupCompatibilityIsolatedSupport P.support group pivot compatible)).realize :=
  partitionedProjectionClosed P _ {pivot}
    (groupCompatibilityIsolatedSupport_isProjectionClosed
      P.support group pivot compatible hsound)

end Restricts

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Group readability survives restricting both the ambient and selected families. -/
theorem HasGroupUniqueLegFibers.restrictToSubset
    {ambient selected smaller : Finset (BlockAddress A)} {group : BlockAddress A → Γ}
    {pivot : Leg} (hunique : HasGroupUniqueLegFibers ambient selected group pivot)
    (hsmaller : smaller ⊆ selected) :
    HasGroupUniqueLegFibers selected smaller group pivot := by
  refine ⟨hsmaller, ?_⟩
  intro address haddress other hother hlabel
  exact hunique.2 address (hsmaller haddress) other (hunique.1 hother) hlabel

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Once a group is readable in an ambient family, it remains readable when that ambient is
replaced by the selected family itself. -/
theorem HasGroupUniqueLegFibers.toSelf
    {ambient selected : Finset (BlockAddress A)} {group : BlockAddress A → Γ}
    {pivot : Leg} (hunique : HasGroupUniqueLegFibers ambient selected group pivot) :
    HasGroupUniqueLegFibers selected selected group pivot := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro address haddress other hother hlabel
  exact hunique.2 address haddress other (hunique.1 hother) hlabel

/-! ## Arbitrary group-stable profile zero-outs -/

/-- A support predicate is stable on a pivot label modulo `group` when it gives the same answer
to ambient addresses with equal pivot labels and equal groups. -/
def IsGroupLabelStable (ambient : Finset (BlockAddress A))
    (group : BlockAddress A → Γ) (pivot : Leg)
    (keep : BlockAddress A → Prop) : Prop :=
  ∀ left ∈ ambient, ∀ right ∈ ambient,
    left pivot = right pivot → group left = group right → (keep left ↔ keep right)

/-- Addresses satisfying one group-and-label-stable profile predicate. -/
noncomputable def groupStableSupport (ambient : Finset (BlockAddress A))
    (keep : BlockAddress A → Prop) : Finset (BlockAddress A) := by
  classical
  exact ambient.filter keep

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem groupStableSupport_subset (ambient : Finset (BlockAddress A))
    (keep : BlockAddress A → Prop) : groupStableSupport ambient keep ⊆ ambient := by
  classical
  intro address haddress
  exact (Finset.mem_filter.mp haddress).1

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- A group-stable address predicate becomes an honest label zero-out once the group is readable
from that label. -/
theorem groupStableSupport_isProjectionClosed
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ) (pivot : Leg)
    (keep : BlockAddress A → Prop)
    (hgroup : HasGroupUniqueLegFibers ambient ambient group pivot)
    (hstable : IsGroupLabelStable ambient group pivot keep) :
    IsProjectionClosed ambient (groupStableSupport ambient keep) {pivot} := by
  classical
  refine ⟨groupStableSupport_subset ambient keep, ?_⟩
  intro address haddress hprojected
  obtain ⟨witness, hwitness, hlabel⟩ := hprojected pivot (by simp)
  have hwitnessData := Finset.mem_filter.mp hwitness
  have hgroupEq : group address = group witness :=
    hgroup.2 witness hwitnessData.1 address haddress hlabel
  apply Finset.mem_filter.mpr
  refine ⟨haddress, ?_⟩
  exact (hstable witness hwitnessData.1 address haddress hlabel.symm hgroupEq.symm).mp
    hwitnessData.2

namespace Restricts

/-- Exact restriction for a profile predicate determined by the pivot label and its readable
coarse group. -/
theorem partitionedGroupStableFilter
    (P : PartitionedTensor (K := K) (A := A) V) (group : BlockAddress A → Γ)
    (pivot : Leg) (keep : BlockAddress A → Prop)
    (hgroup : HasGroupUniqueLegFibers P.support P.support group pivot)
    (hstable : IsGroupLabelStable P.support group pivot keep) :
    Restricts P.realize (P.withSupport (groupStableSupport P.support keep)).realize :=
  partitionedProjectionClosed P _ {pivot}
    (groupStableSupport_isProjectionClosed P.support group pivot keep hgroup hstable)

end Restricts

/-! ## Leg-local group readers and grouped assembly -/

namespace PartitionedTensor

/-- Read a coarse group from a fine block label by choosing any supported address containing it.
Group uniqueness makes the choice irrelevant on supported labels. -/
noncomputable def groupReader (P : PartitionedTensor (K := K) (A := A) V)
    (group : BlockAddress A → Γ) (fallback : Γ) : ∀ c, A c → Γ
  | c, label => if h : ∃ address, address ∈ P.support ∧ address c = label then
      group (Classical.choose h)
    else fallback

theorem groupReader_compatible
    (P : PartitionedTensor (K := K) (A := A) V)
    (group : BlockAddress A → Γ) (fallback : Γ)
    (hunique : ∀ c, HasGroupUniqueLegFibers P.support P.support group c)
    (address : BlockAddress A) (haddress : address ∈ P.support) (c : Leg) :
    P.groupReader group fallback c (address c) = group address := by
  classical
  let hex : ∃ other, other ∈ P.support ∧ other c = address c :=
    ⟨address, haddress, rfl⟩
  rw [groupReader, dif_pos hex]
  have hchosen := Classical.choose_spec hex
  exact (hunique c).2 address haddress (Classical.choose hex) hchosen.1 hchosen.2

/-- Construct the `LegGrouping` needed for indexed assembly from group readability on all legs. -/
noncomputable def LegGrouping.ofGroupUnique
    (P : PartitionedTensor (K := K) (A := A) V)
    (group : BlockAddress A → Γ) (fallback : Γ)
    (hunique : ∀ c, HasGroupUniqueLegFibers P.support P.support group c) :
    P.LegGrouping Γ where
  group := group
  blockGroup := P.groupReader group fallback
  compatible := P.groupReader_compatible group fallback hunique

end PartitionedTensor

namespace Restricts

/-- Paper-faithful grouped two-stage compatibility cleanup.  Hashing makes the coarse group
readable from physical `sigma X`; grouped compatibility isolation does the same for physical
`sigma Y` and `sigma Z`.  The output is an indexed direct sum over coarse groups, whose summands
retain every surviving fine address in that group. -/
theorem partitionedOrientedYZGroupCompatibilityCleanup_to_groupedIndexedDirectSum
    [Fintype Γ] [DecidableEq Γ]
    (sigma : Orientation) (P : PartitionedTensor (K := K) (A := A) V)
    (group : BlockAddress A → Γ) (fallback : Γ)
    (hX : HasGroupUniqueLegFibers P.support P.support group (sigma .X))
    (compatibleY : A (sigma .Y) → BlockAddress A → Prop)
    (hsoundY : IsCompatibilitySound P.support (sigma .Y) compatibleY)
    (compatibleZ : A (sigma .Z) → BlockAddress A → Prop)
    (hsoundZ : IsCompatibilitySound
      (groupCompatibilityIsolatedSupport P.support group (sigma .Y) compatibleY)
      (sigma .Z) compatibleZ) :
    let ySupport := groupCompatibilityIsolatedSupport
      P.support group (sigma .Y) compatibleY
    let zSupport := groupCompatibilityIsolatedSupport
      ySupport group (sigma .Z) compatibleZ
    let PZ := P.withSupport zSupport
    ∃ G : PZ.LegGrouping Γ,
      Restricts P.realize
        (Tensor.indexedDirectSum
          (V := PartitionedTensor.LegGrouping.GroupAmbientFamily
            (K := K) (V := V) (Γ := Γ))
          (fun γ ↦ (G.fiber γ).realize)) := by
  classical
  let ySupport := groupCompatibilityIsolatedSupport
    P.support group (sigma .Y) compatibleY
  let zSupport := groupCompatibilityIsolatedSupport
    ySupport group (sigma .Z) compatibleZ
  let PY := P.withSupport ySupport
  let PZ := P.withSupport zSupport
  have hySubset : ySupport ⊆ P.support :=
    groupCompatibilityIsolatedSupport_subset P.support group (sigma .Y) compatibleY
  have hzSubset : zSupport ⊆ ySupport :=
    groupCompatibilityIsolatedSupport_subset ySupport group (sigma .Z) compatibleZ
  have hY : HasGroupUniqueLegFibers P.support ySupport group (sigma .Y) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      P.support group (sigma .Y) compatibleY hsoundY
  have hZ : HasGroupUniqueLegFibers ySupport zSupport group (sigma .Z) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      ySupport group (sigma .Z) compatibleZ hsoundZ
  have hXFinal : HasGroupUniqueLegFibers zSupport zSupport group (sigma .X) :=
    ((hX.restrictToSubset hySubset).restrictToSubset hzSubset).toSelf
  have hYFinal : HasGroupUniqueLegFibers zSupport zSupport group (sigma .Y) :=
    (hY.restrictToSubset hzSubset).toSelf
  have hZFinal : HasGroupUniqueLegFibers zSupport zSupport group (sigma .Z) :=
    hZ.toSelf
  have hfinal : ∀ pivot,
      HasGroupUniqueLegFibers zSupport zSupport group pivot := by
    intro pivot
    have hpivot : sigma (sigma.symm pivot) = pivot := sigma.apply_symm_apply pivot
    generalize hlogical : sigma.symm pivot = logical at hpivot
    cases logical with
    | X =>
        have : sigma .X = pivot := by simpa [hlogical] using hpivot
        simpa [this] using hXFinal
    | Y =>
        have : sigma .Y = pivot := by simpa [hlogical] using hpivot
        simpa [this] using hYFinal
    | Z =>
        have : sigma .Z = pivot := by simpa [hlogical] using hpivot
        simpa [this] using hZFinal
  let G : PZ.LegGrouping Γ :=
    PartitionedTensor.LegGrouping.ofGroupUnique PZ group fallback (by
      simpa [PZ] using hfinal)
  have hyRestrict : Restricts P.realize PY.realize := by
    simpa [PY, ySupport] using
      partitionedGroupCompatibilityIsolated P group (sigma .Y) compatibleY hsoundY
  have hzRestrict : Restricts PY.realize PZ.realize := by
    simpa [PY, PZ, ySupport, zSupport, PartitionedTensor.withSupport] using
      partitionedGroupCompatibilityIsolated PY group (sigma .Z) compatibleZ hsoundZ
  refine ⟨G, hyRestrict.trans (hzRestrict.trans ?_)⟩
  exact G.restricts_groupedIndexedDirectSum

end Restricts

end AlgebraicComplexity.Tensor
