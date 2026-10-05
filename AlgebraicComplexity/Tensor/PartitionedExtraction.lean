/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Partitioned

/-!
# Projection-induced extraction from partitioned tensors

Hashing and compatibility arguments select labels independently on tensor legs.  This module
states the exact finite condition under which those variable zero-outs retain a prescribed set of
constituents and no cross terms.  It deliberately separates the combinatorial uniqueness proof
from the linear-algebraic zero-out.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Keep precisely the labels appearing in `selected` on the active legs; labels on all other
legs remain unrestricted. -/
def keepProjectedLabels (selected : Finset (BlockAddress A)) (active : Finset Leg)
    (c : Leg) (a : A c) : Prop :=
  c ∉ active ∨ ∃ s ∈ selected, s c = a

/-- A selected support is projection-closed in an ambient support when independently retaining
its labels on the active legs creates neither missing selected addresses nor unwanted cross
addresses. -/
def IsProjectionClosed (ambient selected : Finset (BlockAddress A))
    (active : Finset Leg) : Prop :=
  selected ⊆ ambient ∧
    ∀ u ∈ ambient, (∀ c ∈ active, ∃ s ∈ selected, u c = s c) → u ∈ selected

/-- Addresses of `ambient` retained by the independently selected labels. -/
noncomputable def projectedSupport
    (ambient selected : Finset (BlockAddress A)) (active : Finset Leg) :
    Finset (BlockAddress A) := by
  classical
  exact ambient.filter fun s => ∀ c, keepProjectedLabels selected active c (s c)

/-- Block filter implementing projection-induced variable zeroing. -/
noncomputable def projectedBlockFilter
    (selected : Finset (BlockAddress A)) (active : Finset Leg) :
    ∀ c, PartitionedSpace K V c →ₗ[K] PartitionedSpace K V c := by
  classical
  exact blockFilter (K := K) (V := V) (keepProjectedLabels selected active)

/-- Replace the recorded support while retaining the same typed constituent family. -/
def PartitionedTensor.withSupport
    (P : PartitionedTensor (K := K) (A := A) V)
    (support : Finset (BlockAddress A)) : PartitionedTensor (K := K) (A := A) V where
  support := support
  constituent := P.constituent

/-- Replacing the recorded support exposes exactly the supplied finite set. -/
@[simp] theorem PartitionedTensor.withSupport_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (support : Finset (BlockAddress A)) :
    (P.withSupport support).support = support := rfl

/-- Replacing the recorded support leaves every typed constituent unchanged. -/
@[simp] theorem PartitionedTensor.withSupport_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (support : Finset (BlockAddress A)) (s : BlockAddress A) :
    (P.withSupport support).constituent s = P.constituent s := rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem filter_keepProjectedLabels_eq
    (ambient selected : Finset (BlockAddress A)) (active : Finset Leg)
    (hclosed : IsProjectionClosed ambient selected active) :
    projectedSupport ambient selected active = selected := by
  classical
  unfold projectedSupport
  ext u
  constructor
  · intro hu
    obtain ⟨huAmbient, huKeep⟩ := Finset.mem_filter.mp hu
    apply hclosed.2 u huAmbient
    intro c hc
    have h := huKeep c
    simp only [keepProjectedLabels, hc, not_true_eq_false, false_or] at h
    obtain ⟨s, hs, hsu⟩ := h
    exact ⟨s, hs, hsu.symm⟩
  · intro hu
    apply Finset.mem_filter.mpr
    refine ⟨hclosed.1 hu, ?_⟩
    intro c
    by_cases hc : c ∈ active
    · exact Or.inr ⟨u, hu, rfl⟩
    · exact Or.inl hc

/-- Projection-closed label filtering realizes exactly the prescribed constituent subfamily. -/
theorem map_blockFilter_keepProjectedLabels
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A)) (active : Finset Leg)
    (hclosed : IsProjectionClosed P.support selected active) :
    map (projectedBlockFilter (K := K) (V := V) selected active) P.realize =
      (P.withSupport selected).realize := by
  classical
  unfold projectedBlockFilter
  rw [map_blockFilter_realize]
  unfold PartitionedTensor.realize PartitionedTensor.select PartitionedTensor.withSupport
  change realizePartition (projectedSupport P.support selected active) P.constituent =
    realizePartition selected P.constituent
  rw [filter_keepProjectedLabels_eq P.support selected active hclosed]

namespace Restricts

/-- Tensor-restriction form of projection-closed variable zeroing. -/
theorem partitionedProjectionClosed
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A)) (active : Finset Leg)
    (hclosed : IsProjectionClosed P.support selected active) :
    Restricts P.realize (P.withSupport selected).realize :=
  ⟨projectedBlockFilter (K := K) (V := V) selected active,
    map_blockFilter_keepProjectedLabels P selected active hclosed⟩

end Restricts

/-- Every selected address is the sole ambient address in its fiber on one tensor leg. -/
def HasUniqueLegFibers (ambient selected : Finset (BlockAddress A)) (pivot : Leg) : Prop :=
  selected ⊆ ambient ∧
    ∀ s ∈ selected, ∀ u ∈ ambient, u pivot = s pivot → u = s

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Unique fibers on one leg imply projection closure for that leg. -/
theorem isProjectionClosed_singleton_of_hasUniqueLegFibers
    (ambient selected : Finset (BlockAddress A)) (pivot : Leg)
    (hunique : HasUniqueLegFibers ambient selected pivot) :
    IsProjectionClosed ambient selected {pivot} := by
  refine ⟨hunique.1, ?_⟩
  intro u huAmbient huProjected
  obtain ⟨s, hs, hus⟩ := huProjected pivot (by simp)
  have heq : u = s := hunique.2 s hs u huAmbient hus
  simpa [heq] using hs

/-- Keep all labels on the two non-`X` legs and just the selected labels on the `X` leg. -/
abbrev keepXLabels (selected : Finset (BlockAddress A)) :=
  keepProjectedLabels selected ({.X} : Finset Leg)

namespace Restricts

/-- If selected addresses are the unique ambient occupants of their fibers on any chosen leg,
zeroing all other variables on that leg extracts exactly their constituent subfamily. -/
theorem partitionedUniqueLegFibers
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A)) (pivot : Leg)
    (hunique : HasUniqueLegFibers P.support selected pivot) :
    Restricts P.realize (P.withSupport selected).realize :=
  partitionedProjectionClosed P selected {pivot}
    (isProjectionClosed_singleton_of_hasUniqueLegFibers P.support selected pivot hunique)

/-- If the selected addresses are the unique ambient occupants of their `X`-fibers, zeroing all
other `X` variables extracts exactly their constituent subfamily. -/
theorem partitionedUniqueXFibers
    (P : PartitionedTensor (K := K) (A := A) V)
    (selected : Finset (BlockAddress A))
    (hunique : HasUniqueLegFibers P.support selected .X) :
    Restricts P.realize (P.withSupport selected).realize :=
  partitionedUniqueLegFibers P selected .X hunique

end Restricts

end AlgebraicComplexity.Tensor
