/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing
import AlgebraicComplexity.MatrixMultiplication.MarkedXYPresentPartitionExtraction

set_option autoImplicit false

/-!
# All-leg marked extraction when only some abstract targets are present

This module formalizes the finite tensor statement in the Total-Weight manuscript,
`better_bound/paper.tex:764-796`, Corollary `cor:present-marked-all-leg-extraction`.  Marked affine
hashing isolates an abstract target family against every common-bucket competitor sharing any
tensor leg.  An actual tensor can have smaller support: some abstract targets have no fine preimage.

We split the isolated family into present and missing targets.  The split has an exact cardinality
identity.  Intersecting with actual support preserves both unique ambient fibers and injectivity on
all three legs, so ordinary legwise zeroing exposes a genuine indexed direct sum of precisely the
present constituents.

Missing targets are only recorded here.  This module neither assumes that they have preimages nor
repairs holes inside a present constituent.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

variable {R : Type u} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

namespace PartitionHashEncoding

variable {support : Finset (BlockAddress A)}

/-- Marked all-leg-isolated addresses that actually occur in the tensor partition. -/
noncomputable def presentMarkedLegwiseIsolatedPowerAddresses
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  P.support ∩ H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed

/-- Abstract marked all-leg-isolated targets that do not occur in the tensor partition. -/
noncomputable def missingMarkedLegwiseIsolatedPowerAddresses
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed \ P.support

/-- The abstract marked count is exactly the sum of its missing and present parts.

**Proof sketch.** Apply the standard cardinality formula for a finite set split by intersection
with the actual support. -/
theorem card_missing_add_card_presentMarkedLegwiseIsolatedPowerAddresses
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    (H.missingMarkedLegwiseIsolatedPowerAddresses ambientWords markedWords B seed P).card +
        (H.presentMarkedLegwiseIsolatedPowerAddresses ambientWords markedWords B seed P).card =
      (H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed).card := by
  classical
  simpa only [missingMarkedLegwiseIsolatedPowerAddresses,
    presentMarkedLegwiseIsolatedPowerAddresses, Finset.inter_comm] using
      Finset.card_sdiff_add_card_inter
        (H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed) P.support

/-- A present selected address remains the unique actual hash survivor in its fiber on any chosen
leg.

**Proof sketch.** The abstract selected address is unique among every abstract hash survivor.
Intersect both families with actual support and reuse that uniqueness statement. -/
theorem presentMarkedLegwiseIsolatedPowerAddresses_hasUniqueLegFibers
    [NeZero (2 : R)]
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (physicalLeg : Leg) :
    HasUniqueLegFibers
      (H.presentHashFilteredPowerAddresses ambientWords B seed P)
      (H.presentMarkedLegwiseIsolatedPowerAddresses ambientWords markedWords B seed P)
      physicalLeg := by
  classical
  have hfull := H.markedLegwiseIsolatedPowerAddresses_hasUniqueLegFibers
    n ambientWords markedWords hwords B hB seed physicalLeg
  constructor
  · intro address haddress
    obtain ⟨hpresent, hmarked⟩ := Finset.mem_inter.mp haddress
    exact Finset.mem_inter.mpr ⟨hpresent, hfull.1 hmarked⟩
  · intro selected hselected surviving hsurviving hleg
    exact hfull.2 selected (Finset.mem_inter.mp hselected).2
      surviving (Finset.mem_inter.mp hsurviving).2 hleg

/-- The actually present marked family still uses disjoint variables on all three tensor legs.

**Proof sketch.** Restrict the ambient marked family's legwise injectivity theorem to its
intersection with actual support. -/
theorem presentMarkedLegwiseIsolatedPowerAddresses_isLegwiseInjective
    [NeZero (2 : R)]
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    IsLegwiseInjective
      (H.presentMarkedLegwiseIsolatedPowerAddresses ambientWords markedWords B seed P) := by
  classical
  intro physicalLeg left hleft right hright hleg
  exact H.markedLegwiseIsolatedPowerAddresses_isLegwiseInjective
    n ambientWords markedWords hwords B hB seed physicalLeg
      (Finset.mem_inter.mp hleft).2 (Finset.mem_inter.mp hright).2 hleg

end PartitionHashEncoding

namespace Tensor.Restricts

section TensorExtraction

variable {support : Finset (BlockAddress A)}
variable {K : Type v} [CommSemiring K]
variable {n : ℕ}
variable {V : ∀ c, PositiveWord (A c) n → Type x}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Actual hash survivors restrict to the indexed direct sum of the present marked targets.

**Proof sketch.** Unique `X` fibers zero away all nonselected survivors.  Legwise injectivity of
the remaining support then identifies its realization with the indexed direct sum of its
constituents. -/
theorem presentHashFiltered_to_presentMarkedLegwiseIsolatedIndexedDirectSum
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Restricts
      (P.withSupport (H.presentHashFilteredPowerAddresses ambientWords B seed P)).realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := V)
          (H.presentMarkedLegwiseIsolatedPowerAddresses
            ambientWords markedWords B seed P))
        (fun selected : H.presentMarkedLegwiseIsolatedPowerAddresses
            ambientWords markedWords B seed P ↦ P.constituent selected.1)) := by
  let present := H.presentMarkedLegwiseIsolatedPowerAddresses
    ambientWords markedWords B seed P
  exact (Tensor.Restricts.partitionedUniqueXFibers
      (P.withSupport (H.presentHashFilteredPowerAddresses ambientWords B seed P)) present
      (by
        simpa only [PartitionedTensor.withSupport_support] using
          H.presentMarkedLegwiseIsolatedPowerAddresses_hasUniqueLegFibers
            ambientWords markedWords hwords B hB seed P .X)).trans
    (by
      unfold PartitionedTensor.withSupport
      exact Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum
        ({ support := present, constituent := P.constituent } :
          PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
        (H.presentMarkedLegwiseIsolatedPowerAddresses_isLegwiseInjective
          ambientWords markedWords hwords B hB seed P))

/-- **Present-support all-leg extraction.** An actual modeled subfamily restricts to the indexed
direct sum of exactly those abstract marked isolated targets that it contains.

**Proof sketch.** Apply independent hash zeroing to the actual modeled support, then apply the
preceding present-family direct-sum extraction. -/
theorem presentModeledTargets_to_presentMarkedLegwiseIsolatedIndexedDirectSum
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support ⊆ H.modeledAddresses n (H.legalTargets n ambientWords)) :
    Restricts P.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := V)
          (H.presentMarkedLegwiseIsolatedPowerAddresses
            ambientWords markedWords B seed P))
        (fun selected : H.presentMarkedLegwiseIsolatedPowerAddresses
            ambientWords markedWords B seed P ↦ P.constituent selected.1)) :=
  (Tensor.Restricts.presentModeledTargets_to_presentHashFiltered
      H ambientWords B seed P hsupport).trans
    (Tensor.Restricts.presentHashFiltered_to_presentMarkedLegwiseIsolatedIndexedDirectSum
      H ambientWords markedWords hwords B hB seed P)

end TensorExtraction

end Tensor.Restricts

end AlgebraicComplexity
