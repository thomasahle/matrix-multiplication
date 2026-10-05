/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MarkedXYPartitionedPowerHashing

/-!
# Marked hashing when only some abstract targets are present

The affine-hashing count is naturally carried out in an abstract ambient family of legal words.
In a recursive tensor construction, however, an abstract target need not have a fine preimage in
the approximately selected parent.  The tensor partition therefore need only have support
*contained in* the modeled ambient family, rather than equal to it.

This file separates those two finite objects.  Hashing still chooses an abstract marked isolated
family.  The actual tensor restricts to its intersection with that family.  The complementary
abstract targets are recorded explicitly as missing targets, with an exact cardinality identity.
No nonemptiness or bound on the missing set is assumed; those are the later concentration and
hole-repair obligations.

The construction uses only legwise hash zeroing followed by the already-proved ambient
`X`-fiber uniqueness.  In particular, it does not assume a degeneration of an assembled product.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

variable {R : Type u} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

namespace PartitionHashEncoding

variable {support : Finset (BlockAddress A)}

/-- Hash-filtered addresses that are actually present in `P`. -/
noncomputable def presentHashFilteredPowerAddresses
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  P.support ∩ H.filteredPowerAddresses n words B seed

/-- Marked `X/Y`-isolated addresses that have an actual constituent in `P`. -/
noncomputable def presentMarkedXYIsolatedPowerAddresses
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  P.support ∩ H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed

/-- Abstract marked isolated targets that have no actual constituent in `P`. -/
noncomputable def missingMarkedXYIsolatedPowerAddresses
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed \ P.support

/-- The abstract selected count is the sum of the present and missing counts. -/
theorem card_missing_add_card_presentMarkedXYIsolatedPowerAddresses
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    (H.missingMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P).card +
        (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P).card =
      (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed).card := by
  classical
  simpa only [missingMarkedXYIsolatedPowerAddresses,
    presentMarkedXYIsolatedPowerAddresses, Finset.inter_comm] using
      Finset.card_sdiff_add_card_inter
        (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed) P.support

/-- The present marked family remains `X`-injective. -/
theorem x_injectiveOn_presentMarkedXYIsolatedPowerAddresses
    [NeZero (2 : R)]
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .X)
      (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P : Set _) := by
  apply (H.x_injectiveOn_markedXYIsolatedPowerAddresses
    n ambientWords markedWords hwords B hB seed).mono
  intro address haddress
  exact (Finset.mem_inter.mp haddress).2

/-- The present marked family remains `Y`-injective. -/
theorem y_injectiveOn_presentMarkedXYIsolatedPowerAddresses
    [NeZero (2 : R)]
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .Y)
      (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P : Set _) := by
  apply (H.y_injectiveOn_markedXYIsolatedPowerAddresses
    n ambientWords markedWords hwords B hB seed).mono
  intro address haddress
  exact (Finset.mem_inter.mp haddress).2

/-- Within the actually present hash-filtered family, every present marked address is still the
unique occupant of its `X` fiber. -/
theorem presentMarkedXYIsolatedPowerAddresses_hasUniqueXFibers
    [NeZero (2 : R)]
    {K : Type v} [CommSemiring K] {n : ℕ}
    {V : ∀ c, PositiveWord (A c) n → Type x}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    HasUniqueLegFibers
      (H.presentHashFilteredPowerAddresses ambientWords B seed P)
      (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P) .X := by
  classical
  have hfull := H.markedXYIsolatedPowerAddresses_hasUniqueXFibers
    n ambientWords markedWords hwords B hB seed
  constructor
  · intro address haddress
    obtain ⟨hpresent, hmarked⟩ := Finset.mem_inter.mp haddress
    exact Finset.mem_inter.mpr ⟨hpresent, hfull.1 hmarked⟩
  · intro selected hselected surviving hsurviving hx
    exact hfull.2 selected (Finset.mem_inter.mp hselected).2
      surviving (Finset.mem_inter.mp hsurviving).2 hx

section TensorExtraction

variable {K : Type v} [CommSemiring K]
variable {n : ℕ}
variable {V : ∀ c, PositiveWord (A c) n → Type x}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Independent hash-block zeroing works for any actually present subfamily of the abstract
modeled ambient family. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.presentModeledTargets_to_presentHashFiltered
    (H : PartitionHashEncoding (R := R) support)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support ⊆ H.modeledAddresses n (H.legalTargets n words)) :
    Restricts P.realize
      (P.withSupport (H.presentHashFilteredPowerAddresses words B seed P)).realize := by
  classical
  let keep := H.hashKeepBlock n B seed
  have hselect := Tensor.Restricts.partitionedSelect P keep
  apply hselect.trans (Tensor.Restricts.of_eq ?_)
  have hselectedSupport : (P.select keep).support =
      H.presentHashFilteredPowerAddresses words B seed P := by
    change P.support.filter (fun s ↦ ∀ c, H.hashKeepBlock n B seed c (s c)) =
      P.support ∩ H.filteredPowerAddresses n words B seed
    ext address
    constructor
    · intro haddress
      obtain ⟨hpresent, hkeep⟩ := Finset.mem_filter.mp haddress
      apply Finset.mem_inter.mpr
      refine ⟨hpresent, ?_⟩
      rw [← H.filter_modeledAddresses_hashKeepBlock_eq n words B seed]
      exact Finset.mem_filter.mpr ⟨hsupport hpresent, hkeep⟩
    · intro haddress
      obtain ⟨hpresent, hfiltered⟩ := Finset.mem_inter.mp haddress
      apply Finset.mem_filter.mpr
      refine ⟨hpresent, ?_⟩
      rw [← H.filter_modeledAddresses_hashKeepBlock_eq n words B seed] at hfiltered
      exact (Finset.mem_filter.mp hfiltered).2
  unfold PartitionedTensor.realize
  change realizePartition (P.select keep).support P.constituent =
    realizePartition (H.presentHashFilteredPowerAddresses words B seed P) P.constituent
  rw [hselectedSupport]

/-- Actual hash survivors restrict to the present part of the abstract marked isolated family. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.presentHashFiltered_to_presentMarkedXYIsolated
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V) :
    Restricts
      (P.withSupport (H.presentHashFilteredPowerAddresses ambientWords B seed P)).realize
      (P.withSupport
        (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P)).realize := by
  have hrestrict := Tensor.Restricts.partitionedUniqueXFibers
    (P.withSupport (H.presentHashFilteredPowerAddresses ambientWords B seed P))
    (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P)
    (by
      simpa only [PartitionedTensor.withSupport_support] using
        H.presentMarkedXYIsolatedPowerAddresses_hasUniqueXFibers
          ambientWords markedWords hwords B hB seed P)
  simpa only [PartitionedTensor.withSupport] using hrestrict

/-- **Present-support marked extraction.**  Equality with the abstract ambient support is not
required: the actual tensor restricts to exactly those abstract marked isolated targets that have
an actual constituent. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.presentModeledTargets_to_presentMarkedXYIsolated
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support ⊆ H.modeledAddresses n (H.legalTargets n ambientWords)) :
    Restricts P.realize
      (P.withSupport
        (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P)).realize :=
  (Tensor.Restricts.presentModeledTargets_to_presentHashFiltered
      H ambientWords B seed P hsupport).trans
    (Tensor.Restricts.presentHashFiltered_to_presentMarkedXYIsolated
      H ambientWords markedWords hwords B hB seed P)

end TensorExtraction

end PartitionHashEncoding

end AlgebraicComplexity
