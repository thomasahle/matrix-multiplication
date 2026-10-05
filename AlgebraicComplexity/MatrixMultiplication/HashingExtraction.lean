/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TwoLegHashingExtraction
import AlgebraicComplexity.Tensor.PartitionedDirectSum

/-!
# Laser-method tensor interface for asymmetric hashing extraction

This module is the narrow adapter between the reusable finite hashing theorem and partitioned
tensor variable zeroing.  The same theorem is consumed at the global and recursive constituent
stages: only the concrete finite family of legal block triples changes.
-/

namespace AlgebraicComplexity

universe u v w x

namespace ProgressionHash

/-- All three legs of a word-indexed hashing instance use words over the same finite field. -/
abbrev WordBlockLabels (R : Type u) (ι : Type v) (_ : Tensor.Leg) := ι → R

namespace LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

noncomputable local instance : DecidableEq ι := Classical.decEq _

noncomputable local instance (c : Tensor.Leg) [Fintype R] :
    Fintype (WordBlockLabels R ι c) := inferInstance

noncomputable local instance (c : Tensor.Leg) :
    DecidableEq (WordBlockLabels R ι c) := Classical.decEq _

/-- The partitioned-tensor address represented by a legal hashing triple. -/
def blockAddress (triple : LegalTriple R ι target) :
    Tensor.BlockAddress (WordBlockLabels R ι) :=
  Tensor.ofLegs triple.xIndex triple.yIndex triple.zIndex

omit [Fintype ι] in
@[simp] theorem blockAddress_X (triple : LegalTriple R ι target) :
    triple.blockAddress .X = triple.xIndex := rfl

omit [Fintype ι] in
@[simp] theorem blockAddress_Y (triple : LegalTriple R ι target) :
    triple.blockAddress .Y = triple.yIndex := rfl

omit [Fintype ι] in
@[simp] theorem blockAddress_Z (triple : LegalTriple R ι target) :
    triple.blockAddress .Z = triple.zIndex := rfl

omit [Fintype ι] in
/-- A three-leg block address remembers its legal triple. -/
theorem blockAddress_injective :
    Function.Injective (blockAddress : LegalTriple R ι target →
      Tensor.BlockAddress (WordBlockLabels R ι)) := by
  intro left right h
  apply LegalTriple.ext
  · exact congrFun h .X
  · exact congrFun h .Y
  · exact congrFun h .Z

/-- Hash-filtered block addresses. -/
noncomputable def filteredAddresses
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    Finset (Tensor.BlockAddress (WordBlockLabels R ι)) := by
  classical
  exact (filteredTargets targets B seed).image blockAddress

/-- Isolated block addresses selected by the more-asymmetric cleanup. -/
noncomputable def xIsolatedAddresses
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    Finset (Tensor.BlockAddress (WordBlockLabels R ι)) := by
  classical
  exact (xIsolatedTargets targets B seed).image blockAddress

/-- Passing from isolated legal triples to block addresses loses no copies. -/
theorem card_xIsolatedAddresses
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    (xIsolatedAddresses targets B seed).card =
      (xIsolatedTargets targets B seed).card := by
  classical
  unfold xIsolatedAddresses
  exact Finset.card_image_of_injOn blockAddress_injective.injOn

/-- Passing from filtered legal triples to block addresses likewise preserves cardinality. -/
theorem card_filteredAddresses
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    (filteredAddresses targets B seed).card =
      (filteredTargets targets B seed).card := by
  classical
  unfold filteredAddresses
  exact Finset.card_image_of_injOn blockAddress_injective.injOn

/-- The isolated address family is contained in the hash-filtered address family. -/
theorem xIsolatedAddresses_subset_filteredAddresses [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    xIsolatedAddresses targets B seed ⊆ filteredAddresses targets B seed := by
  classical
  exact Finset.image_mono blockAddress
    (xIsolatedTargets_subset_filteredTargets targets B seed)

/-- The combinatorial isolation theorem gives exactly the unique-`X`-fiber hypothesis required
by the partitioned tensor zero-out theorem. -/
theorem xIsolatedAddresses_hasUniqueXFibers [Fintype R] [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι) :
    Tensor.HasUniqueLegFibers (filteredAddresses targets B seed)
      (xIsolatedAddresses targets B seed) .X := by
  classical
  refine ⟨xIsolatedAddresses_subset_filteredAddresses targets B seed, ?_⟩
  intro selected hselected surviving hsurviving hx
  unfold xIsolatedAddresses at hselected
  unfold filteredAddresses at hsurviving
  obtain ⟨triple, htriple, rfl⟩ := Finset.mem_image.mp hselected
  obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hsurviving
  have heq : other = triple :=
    eq_of_mem_xIsolatedTargets_of_mem_filteredTargets targets B hB seed htriple hother
      (by simpa using hx)
  subst other
  rfl

section TensorZeroOut

variable {K : Type w} [CommSemiring K]
variable {V : ∀ c, WordBlockLabels R ι c → Type x}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Exact tensor zero-out following asymmetric hashing.  Any partitioned tensor whose support is
the hash-filtered legal family restricts to precisely the isolated family by zeroing `X` blocks.
This statement is shared verbatim by global and recursive constituent clients. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.hashFiltered_to_xIsolated
    [Fintype R] [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι)
    (P : Tensor.PartitionedTensor (K := K) (A := WordBlockLabels R ι) V)
    (hsupport : P.support = filteredAddresses targets B seed) :
    Tensor.Restricts P.realize (P.withSupport (xIsolatedAddresses targets B seed)).realize := by
  apply Tensor.Restricts.partitionedUniqueXFibers P (xIsolatedAddresses targets B seed)
  rw [hsupport]
  exact xIsolatedAddresses_hasUniqueXFibers targets B hB seed

/-- Complete finite tensor interface.  Once later compatibility cleanup establishes injectivity
on every leg of the isolated support, hashing followed by interface extraction restricts the
original filtered tensor to a genuine indexed direct sum of the surviving constituents. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.hashFiltered_to_xIsolatedIndexedDirectSum
    [Fintype R] [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι)
    (P : Tensor.PartitionedTensor (K := K) (A := WordBlockLabels R ι) V)
    (hsupport : P.support = filteredAddresses targets B seed)
    (hlegwise : Tensor.IsLegwiseInjective (xIsolatedAddresses targets B seed)) :
    Tensor.Restricts P.realize
      (Tensor.indexedDirectSum
        (V := Tensor.SelectedBlockFamily (V := V) (xIsolatedAddresses targets B seed))
        (fun s : xIsolatedAddresses targets B seed => P.constituent s.1)) := by
  exact (Tensor.Restricts.hashFiltered_to_xIsolated targets B hB seed P hsupport).trans
    (Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum
      (P.withSupport (xIsolatedAddresses targets B seed)) hlegwise)

end TensorZeroOut

end LegalTriple

end ProgressionHash

end AlgebraicComplexity
