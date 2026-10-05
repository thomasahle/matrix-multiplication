/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedDirectSum

/-!
# Compatibility-based variable zeroing

This module packages the exact finite step called "compatibility zero-out II" in recursive laser
arguments.  It is independent of the concrete definition of compatibility.  Once every ambient
address is sound for the label it uses, deleting every label compatible with more than one
address produces unique fibers and therefore an exact tensor restriction.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Every surviving address is compatible with the label it actually uses on `pivot`.  This is
the conclusion of the paper's first compatibility zero-out. -/
def IsCompatibilitySound (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) : Prop :=
  ∀ address ∈ ambient, compatible (address pivot) address

/-- An address survives the unique-compatibility cleanup when it is the sole ambient address
compatible with its label on `pivot`. -/
def IsUniquelyCompatible (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) (address : BlockAddress A) : Prop :=
  address ∈ ambient ∧
    ∀ other ∈ ambient, compatible (address pivot) other → other = address

/-- The support remaining after deleting every `pivot` label compatible with multiple ambient
addresses. -/
noncomputable def compatibilityIsolatedSupport
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) : Finset (BlockAddress A) := by
  classical
  exact ambient.filter (IsUniquelyCompatible ambient pivot compatible)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem mem_compatibilityIsolatedSupport
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) (address : BlockAddress A) :
    address ∈ compatibilityIsolatedSupport ambient pivot compatible ↔
      IsUniquelyCompatible ambient pivot compatible address := by
  classical
  simp [compatibilityIsolatedSupport, IsUniquelyCompatible]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem compatibilityIsolatedSupport_subset
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) :
    compatibilityIsolatedSupport ambient pivot compatible ⊆ ambient := by
  classical
  intro address haddress
  exact (mem_compatibilityIsolatedSupport ambient pivot compatible address).mp haddress |>.1

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Unique-compatibility cleanup produces exactly the unique-fiber certificate required for
legwise variable zeroing. -/
theorem compatibilityIsolatedSupport_hasUniqueLegFibers
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound ambient pivot compatible) :
    HasUniqueLegFibers ambient (compatibilityIsolatedSupport ambient pivot compatible) pivot := by
  classical
  refine ⟨?_, ?_⟩
  · intro address haddress
    exact (mem_compatibilityIsolatedSupport ambient pivot compatible address).mp haddress |>.1
  · intro selected hselected other hother hlabel
    have hunique :=
      (mem_compatibilityIsolatedSupport ambient pivot compatible selected).mp hselected |>.2
    apply hunique other hother
    simpa only [hlabel] using hsound other hother

namespace Restricts

/-- Exact tensor restriction implementing compatibility zero-out II on an arbitrary tensor leg. -/
theorem partitionedCompatibilityIsolated
    (P : PartitionedTensor (K := K) (A := A) V) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (hsound : IsCompatibilitySound P.support pivot compatible) :
    Restricts P.realize
      (P.withSupport
        (compatibilityIsolatedSupport P.support pivot compatible)).realize :=
  AlgebraicComplexity.Tensor.Restricts.partitionedUniqueLegFibers P
    (compatibilityIsolatedSupport P.support pivot compatible) pivot
    (compatibilityIsolatedSupport_hasUniqueLegFibers P.support pivot compatible hsound)

end Restricts

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Fiber uniqueness is inherited when the ambient and selected families are both restricted to
a smaller selected support.  This lets an `X`-isolation certificate survive later `Y`- and
`Z`-compatibility zero-outs. -/
theorem HasUniqueLegFibers.restrictToSubset
    {ambient selected smaller : Finset (BlockAddress A)} {pivot : Leg}
    (hunique : HasUniqueLegFibers ambient selected pivot)
    (hsmaller : smaller ⊆ selected) :
    HasUniqueLegFibers selected smaller pivot := by
  refine ⟨hsmaller, ?_⟩
  intro address haddress other hother hlabel
  exact hunique.2 address (hsmaller haddress) other (hunique.1 hother) hlabel

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Unique fibers on all three legs are precisely legwise injectivity of the selected support. -/
theorem isLegwiseInjective_of_uniqueFibers
    (selected : Finset (BlockAddress A))
    (hunique : ∀ pivot, HasUniqueLegFibers selected selected pivot) :
    IsLegwiseInjective selected := by
  intro pivot left hleft right hright hlabel
  exact ((hunique pivot).2 left hleft right hright hlabel.symm).symm

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Unique ambient fibers imply pairwise distinct selected labels even when the ambient support is
strictly larger than the selected support. -/
theorem isLegwiseInjective_of_uniqueAmbientFibers
    (ambient selected : Finset (BlockAddress A))
    (hunique : ∀ pivot, HasUniqueLegFibers ambient selected pivot) :
    IsLegwiseInjective selected := by
  intro pivot left hleft right hright hlabel
  exact ((hunique pivot).2 left hleft right ((hunique pivot).1 hright) hlabel.symm).symm

namespace Restricts

/-- Paper-facing two-stage compatibility cleanup.

Hashing has already isolated `X` labels.  Sound `Y` compatibility followed by sound `Z`
compatibility deletes multiply-compatible labels.  The final support is independent on every
leg, so the two exact variable zero-outs terminate in a genuine indexed tensor direct sum. -/
theorem partitionedYZCompatibilityCleanup_to_indexedDirectSum
    (P : PartitionedTensor (K := K) (A := A) V)
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address .X) P.support)
    (compatibleY : A .Y → BlockAddress A → Prop)
    (hsoundY : IsCompatibilitySound P.support .Y compatibleY)
    (compatibleZ : A .Z → BlockAddress A → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ) :
    let ySupport := compatibilityIsolatedSupport P.support .Y compatibleY
    let zSupport := compatibilityIsolatedSupport ySupport .Z compatibleZ
    Restricts P.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := V) zSupport)
        (fun address : zSupport ↦ P.constituent address.1)) := by
  classical
  let ySupport := compatibilityIsolatedSupport P.support .Y compatibleY
  let zSupport := compatibilityIsolatedSupport ySupport .Z compatibleZ
  let PY := P.withSupport ySupport
  let PZ : PartitionedTensor (K := K) (A := A) V :=
    { support := zSupport, constituent := P.constituent }
  have hySubset : ySupport ⊆ P.support := by
    exact compatibilityIsolatedSupport_subset P.support .Y compatibleY
  have hzSubset : zSupport ⊆ ySupport := by
    exact compatibilityIsolatedSupport_subset ySupport .Z compatibleZ
  have hXUnique : HasUniqueLegFibers P.support P.support .X := by
    refine ⟨Finset.Subset.rfl, ?_⟩
    intro left hleft right hright hlabel
    exact hX hright hleft hlabel
  have hYUnique : HasUniqueLegFibers P.support ySupport .Y :=
    compatibilityIsolatedSupport_hasUniqueLegFibers P.support .Y compatibleY hsoundY
  have hZUnique : HasUniqueLegFibers ySupport zSupport .Z :=
    compatibilityIsolatedSupport_hasUniqueLegFibers ySupport .Z compatibleZ hsoundZ
  have hXFinal : HasUniqueLegFibers ySupport zSupport .X :=
    (hXUnique.restrictToSubset hySubset).restrictToSubset hzSubset
  have hYFinal : HasUniqueLegFibers ySupport zSupport .Y :=
    hYUnique.restrictToSubset hzSubset
  have hfinal : IsLegwiseInjective zSupport :=
    isLegwiseInjective_of_uniqueAmbientFibers ySupport zSupport fun pivot ↦ by
      cases pivot with
      | X => exact hXFinal
      | Y => exact hYFinal
      | Z => exact hZUnique
  have hyRestrict : Restricts P.realize PY.realize := by
    simpa [PY, ySupport] using
      partitionedCompatibilityIsolated P .Y compatibleY hsoundY
  have hzRestrict : Restricts PY.realize PZ.realize := by
    simpa [PY, PZ, ySupport, zSupport, PartitionedTensor.withSupport] using
      partitionedCompatibilityIsolated PY .Z compatibleZ hsoundZ
  have hdirect : Restricts PZ.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := V) zSupport)
        (fun address : zSupport ↦ P.constituent address.1)) := by
    exact partitionedLegwiseInjective_to_indexedDirectSum PZ hfinal
  exact hyRestrict.trans (hzRestrict.trans hdirect)

end Restricts

end AlgebraicComplexity.Tensor
