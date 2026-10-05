/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibility

/-!
# Orientation transport for asymmetric compatibility cleanup

The compatibility proof is written once in logical coordinates `X,Y,Z`.  A region orientation
`sigma` interprets logical leg `c` as physical leg `sigma c`.  This file transports block
addresses, the concrete `Y`/`Z` predicates, and their soundness witnesses along an arbitrary
`Tensor.Orientation`; no enumeration of the six permutations is used.

The transported predicates have pivots `sigma Y` and `sigma Z`, exactly as required by the
generic compatibility-zeroing API.  The model itself is stated over the logically reindexed
label family `c ↦ A (sigma c)`, so a concrete block encoder only has to prove the identity-order
model once after choosing the logical view of a region.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v w x

/-- The label family seen in logical coordinates under a physical region orientation. -/
abbrev OrientedLabelFamily (sigma : Orientation) (A : Leg → Type v) (c : Leg) :=
  A (sigma c)

/-- Reindex logical block addresses to physical block addresses.  This is Mathlib's dependent
Pi-family reindexing equivalence, specialized to the three tensor legs. -/
def orientedBlockAddressEquiv (sigma : Orientation) (A : Leg → Type v) :
    BlockAddress (OrientedLabelFamily sigma A) ≃ BlockAddress A :=
  Equiv.piCongrLeft A sigma

/-- View a physical block address in the logical coordinates of one oriented region. -/
def logicalAddress (sigma : Orientation) {A : Leg → Type v}
    (address : BlockAddress A) : BlockAddress (OrientedLabelFamily sigma A) :=
  (orientedBlockAddressEquiv sigma A).symm address

@[simp] theorem logicalAddress_apply (sigma : Orientation) {A : Leg → Type v}
    (address : BlockAddress A) (c : Leg) :
    logicalAddress sigma address c = address (sigma c) := by
  exact Equiv.piCongrLeft_symm_apply A sigma address c

@[simp] theorem orientedBlockAddressEquiv_logicalAddress
    (sigma : Orientation) {A : Leg → Type v} (address : BlockAddress A) :
    orientedBlockAddressEquiv sigma A (logicalAddress sigma address) = address :=
  (orientedBlockAddressEquiv sigma A).apply_symm_apply address

/-! ## Tensor cleanup on oriented physical legs -/

/-- Two-stage compatibility cleanup on the physical legs `sigma Y` and `sigma Z`, assuming
hashing isolated the physical leg `sigma X`.  This is the orientation-parametric form of
`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum`; its proof uses only
that `sigma` is a permutation of all three legs. -/
theorem partitionedOrientedYZCompatibilityCleanup_to_indexedDirectSum
    {K : Type w} [CommSemiring K]
    {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (sigma : Orientation) (P : PartitionedTensor (K := K) (A := A) V)
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address (sigma .X)) P.support)
    (compatibleY : A (sigma .Y) → BlockAddress A → Prop)
    (hsoundY : IsCompatibilitySound P.support (sigma .Y) compatibleY)
    (compatibleZ : A (sigma .Z) → BlockAddress A → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport P.support (sigma .Y) compatibleY)
      (sigma .Z) compatibleZ) :
    let ySupport := compatibilityIsolatedSupport P.support (sigma .Y) compatibleY
    let zSupport := compatibilityIsolatedSupport ySupport (sigma .Z) compatibleZ
    Restricts P.realize
      (indexedDirectSum
        (V := SelectedBlockFamily (V := V) zSupport)
        (fun address : zSupport ↦ P.constituent address.1)) := by
  classical
  let ySupport := compatibilityIsolatedSupport P.support (sigma .Y) compatibleY
  let zSupport := compatibilityIsolatedSupport ySupport (sigma .Z) compatibleZ
  let PY := P.withSupport ySupport
  let PZ : PartitionedTensor (K := K) (A := A) V :=
    { support := zSupport, constituent := P.constituent }
  have hySubset : ySupport ⊆ P.support :=
    compatibilityIsolatedSupport_subset P.support (sigma .Y) compatibleY
  have hzSubset : zSupport ⊆ ySupport :=
    compatibilityIsolatedSupport_subset ySupport (sigma .Z) compatibleZ
  have hXUnique : HasUniqueLegFibers P.support P.support (sigma .X) := by
    refine ⟨Finset.Subset.rfl, ?_⟩
    intro left hleft right hright hlabel
    exact hX hright hleft hlabel
  have hYUnique : HasUniqueLegFibers P.support ySupport (sigma .Y) :=
    compatibilityIsolatedSupport_hasUniqueLegFibers
      P.support (sigma .Y) compatibleY hsoundY
  have hZUnique : HasUniqueLegFibers ySupport zSupport (sigma .Z) :=
    compatibilityIsolatedSupport_hasUniqueLegFibers
      ySupport (sigma .Z) compatibleZ hsoundZ
  have hXFinal : HasUniqueLegFibers ySupport zSupport (sigma .X) :=
    (hXUnique.restrictToSubset hySubset).restrictToSubset hzSubset
  have hYFinal : HasUniqueLegFibers ySupport zSupport (sigma .Y) :=
    hYUnique.restrictToSubset hzSubset
  have hfinal : IsLegwiseInjective zSupport :=
    isLegwiseInjective_of_uniqueAmbientFibers ySupport zSupport fun pivot ↦ by
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
          simpa [this] using hZUnique
  have hyRestrict : Restricts P.realize PY.realize := by
    simpa [PY, ySupport] using
      Tensor.Restricts.partitionedCompatibilityIsolated
        P (sigma .Y) compatibleY hsoundY
  have hzRestrict : Restricts PY.realize PZ.realize := by
    simpa [PY, PZ, ySupport, zSupport, PartitionedTensor.withSupport] using
      Tensor.Restricts.partitionedCompatibilityIsolated
        PY (sigma .Z) compatibleZ hsoundZ
  have hdirect : Restricts PZ.realize
      (indexedDirectSum
        (V := SelectedBlockFamily (V := V) zSupport)
        (fun address : zSupport ↦ P.constituent address.1)) :=
    Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum PZ hfinal
  exact hyRestrict.trans (hzRestrict.trans hdirect)

/-- The logical `Y` predicate interpreted on physical leg `sigma Y`. -/
def OrientedCompatibleY {A : Leg → Type v} {Part : Type u} [DecidableEq Part]
    {depth samples : ℕ} (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (label : A (sigma .Y)) (address : BlockAddress A) : Prop :=
  model.CompatibleY targets label (logicalAddress sigma address)

/-- The logical `Z` predicate interpreted on physical leg `sigma Z`. -/
def OrientedCompatibleZ {A : Leg → Type v} {Part : Type u} [DecidableEq Part]
    {depth samples : ℕ} (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (label : A (sigma .Z)) (address : BlockAddress A) : Prop :=
  model.CompatibleZ targets label (logicalAddress sigma address)

namespace CompatibilityModel

variable {A : Leg → Type v} {Part : Type u} [DecidableEq Part]
variable {depth samples : ℕ}

/-- Pointwise transport of the identity-order `Y` compatibility theorem to an arbitrary region
orientation. -/
theorem orientedCompatibleY_of_passesYFirstZeroOut
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth) (address : BlockAddress A)
    (hpasses : model.PassesYFirstZeroOut targets (logicalAddress sigma address)) :
    OrientedCompatibleY sigma model targets (address (sigma .Y)) address := by
  simpa [OrientedCompatibleY] using
    model.compatibleY_of_passesYFirstZeroOut targets
      (logicalAddress sigma address) hpasses

/-- Pointwise transport of the identity-order `Z` compatibility theorem to an arbitrary region
orientation. -/
theorem orientedCompatibleZ_of_passesZFirstZeroOut
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth) (address : BlockAddress A)
    (hpasses : model.PassesZFirstZeroOut targets (logicalAddress sigma address)) :
    OrientedCompatibleZ sigma model targets (address (sigma .Z)) address := by
  simpa [OrientedCompatibleZ] using
    model.compatibleZ_of_passesZFirstZeroOut targets
      (logicalAddress sigma address) hpasses

/-- Soundness of the oriented `Y` predicate on a physical support. -/
theorem orientedYCompatibility_sound [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (ambient : Finset (BlockAddress A))
    (hpasses : ∀ address ∈ ambient,
      model.PassesYFirstZeroOut targets (logicalAddress sigma address)) :
    IsCompatibilitySound ambient (sigma .Y)
      (OrientedCompatibleY sigma model targets) := by
  intro address haddress
  exact model.orientedCompatibleY_of_passesYFirstZeroOut sigma targets address
    (hpasses address haddress)

/-- Soundness of the oriented `Z` predicate on a physical support. -/
theorem orientedZCompatibility_sound [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (ambient : Finset (BlockAddress A))
    (hpasses : ∀ address ∈ ambient,
      model.PassesZFirstZeroOut targets (logicalAddress sigma address)) :
    IsCompatibilitySound ambient (sigma .Z)
      (OrientedCompatibleZ sigma model targets) := by
  intro address haddress
  exact model.orientedCompatibleZ_of_passesZFirstZeroOut sigma targets address
    (hpasses address haddress)

/-- After oriented `Y` isolation, oriented `Z` soundness follows by restricting the ambient
first-zero-out invariants to the smaller support. -/
theorem orientedZCompatibility_sound_afterY
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (ambient : Finset (BlockAddress A))
    (hpasses : ∀ address ∈ ambient,
      model.PassesZFirstZeroOut targets (logicalAddress sigma address)) :
    IsCompatibilitySound
      (compatibilityIsolatedSupport ambient (sigma .Y)
        (OrientedCompatibleY sigma model targets))
      (sigma .Z) (OrientedCompatibleZ sigma model targets) := by
  apply model.orientedZCompatibility_sound sigma targets
  intro address haddress
  exact hpasses address
    (compatibilityIsolatedSupport_subset ambient (sigma .Y)
      (OrientedCompatibleY sigma model targets) haddress)

/-- Arbitrary-orientation version of `yzCompatibility_sound`, packaged in the exact sequential
shape consumed by compatibility zeroing.  No distinctness or enumeration hypothesis on `sigma`
appears. -/
theorem orientedYZCompatibility_sound
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (ambient : Finset (BlockAddress A))
    (hpassesY : ∀ address ∈ ambient,
      model.PassesYFirstZeroOut targets (logicalAddress sigma address))
    (hpassesZ : ∀ address ∈ ambient,
      model.PassesZFirstZeroOut targets (logicalAddress sigma address)) :
    IsCompatibilitySound ambient (sigma .Y)
        (OrientedCompatibleY sigma model targets) ∧
      IsCompatibilitySound
        (compatibilityIsolatedSupport ambient (sigma .Y)
          (OrientedCompatibleY sigma model targets))
        (sigma .Z) (OrientedCompatibleZ sigma model targets) :=
  ⟨model.orientedYCompatibility_sound sigma targets ambient hpassesY,
    model.orientedZCompatibility_sound_afterY sigma targets ambient hpassesZ⟩

/-- End-to-end oriented compatibility cleanup from the concrete first-zero-out invariants to an
indexed tensor direct sum.  This is the physical-region adapter used after hashing has isolated
logical `X` (physical `sigma X`). -/
theorem orientedCompatibilityCleanup_to_indexedDirectSum
    {K : Type w} [CommSemiring K]
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (sigma : Orientation)
    (model : CompatibilityModel (OrientedLabelFamily sigma A) Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (P : PartitionedTensor (K := K) (A := A) V)
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address (sigma .X)) P.support)
    (hpassesY : ∀ address ∈ P.support,
      model.PassesYFirstZeroOut targets (logicalAddress sigma address))
    (hpassesZ : ∀ address ∈ P.support,
      model.PassesZFirstZeroOut targets (logicalAddress sigma address)) :
    let ySupport := compatibilityIsolatedSupport P.support (sigma .Y)
      (OrientedCompatibleY sigma model targets)
    let zSupport := compatibilityIsolatedSupport ySupport (sigma .Z)
      (OrientedCompatibleZ sigma model targets)
    Restricts P.realize
      (indexedDirectSum
        (V := SelectedBlockFamily (V := V) zSupport)
        (fun address : zSupport ↦ P.constituent address.1)) := by
  obtain ⟨hsoundY, hsoundZ⟩ :=
    model.orientedYZCompatibility_sound sigma targets P.support hpassesY hpassesZ
  exact partitionedOrientedYZCompatibilityCleanup_to_indexedDirectSum
    sigma P hX (OrientedCompatibleY sigma model targets) hsoundY
      (OrientedCompatibleZ sigma model targets) hsoundZ

end CompatibilityModel

end MoreAsymmetryCompatibility
end AlgebraicComplexity
