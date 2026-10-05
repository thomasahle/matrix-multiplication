/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.PartitionedExtraction

/-!
# Grouping a partitioned tensor into indexed component tensors

A support grouping assigns each supported full block address to a finite group, with the group
recoverable independently from every leg's block label.  The latter condition is exactly what is
needed to route variables by legwise linear maps.  The main theorem restricts the realization to
the indexed direct sum of its group fibers.

This abstraction covers the shared-Z groups in the Coppersmith--Winograd `112` construction:
the Z label gives the group directly, while global X/Y isolation makes that same Z group
recoverable from an X or Y block label.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {Γ : Type x} [Fintype Γ] [DecidableEq Γ]

namespace PartitionedTensor

/-- A finite grouping of a partitioned support whose group is independently readable on every
leg. -/
structure LegGrouping (P : PartitionedTensor (K := K) (A := A) V) (Γ : Type x) where
  /-- Group assigned to a full block address.  Values outside the support are irrelevant. -/
  group : BlockAddress A → Γ
  /-- Group read from one block label on one leg. -/
  blockGroup : ∀ c, A c → Γ
  /-- Every supported address receives the same group from all three leg-local readers. -/
  compatible : ∀ s ∈ P.support, ∀ c, blockGroup c (s c) = group s

/-- Read the Z label attached to an X- or Y-isolated support block.  The fallback value is used
only for block labels which do not occur in the support. -/
noncomputable def zGroupReader
    (P : PartitionedTensor (K := K) (A := A) V) (z₀ : A .Z) :
    (c : Leg) → A c → A .Z
  | .X, x => if h : ∃ s, s ∈ P.support ∧ s .X = x then
      (Classical.choose h) .Z
    else z₀
  | .Y, y => if h : ∃ s, s ∈ P.support ∧ s .Y = y then
      (Classical.choose h) .Z
    else z₀
  | .Z, z => z

/-- If the support is injective on X and Y, `zGroupReader` recovers the Z coordinate of every
supported address.

Proof sketch: for X and Y, choose a supported address with the prescribed block label.  Support
injectivity identifies the chosen address with the original one, so their Z labels agree.  The Z
case is true by definition. -/
theorem zGroupReader_compatible
    (P : PartitionedTensor (K := K) (A := A) V) (z₀ : A .Z)
    (hx : Set.InjOn (fun s : BlockAddress A ↦ s .X) P.support)
    (hy : Set.InjOn (fun s : BlockAddress A ↦ s .Y) P.support)
    (s : BlockAddress A) (hs : s ∈ P.support) (c : Leg) :
    zGroupReader P z₀ c (s c) = s .Z := by
  classical
  cases c with
  | X =>
      let hex : ∃ t, t ∈ P.support ∧ t .X = s .X := ⟨s, hs, rfl⟩
      rw [zGroupReader, dif_pos hex]
      have ht := Classical.choose_spec hex
      have hts : Classical.choose hex = s := hx ht.1 hs ht.2
      rw [hts]
  | Y =>
      let hex : ∃ t, t ∈ P.support ∧ t .Y = s .Y := ⟨s, hs, rfl⟩
      rw [zGroupReader, dif_pos hex]
      have ht := Classical.choose_spec hex
      have hts : Classical.choose hex = s := hy ht.1 hs ht.2
      rw [hts]
  | Z => rfl

/-- Group an X/Y-isolated partitioned support by its shared Z block.

The fallback block `z₀` has no semantic effect: it is consulted only on source block labels that
do not occur in the support and hence contribute nothing to the realized tensor. -/
noncomputable def LegGrouping.byZ
    (P : PartitionedTensor (K := K) (A := A) V) (z₀ : A .Z)
    (hx : Set.InjOn (fun s : BlockAddress A ↦ s .X) P.support)
    (hy : Set.InjOn (fun s : BlockAddress A ↦ s .Y) P.support) :
    P.LegGrouping (A .Z) where
  group s := s .Z
  blockGroup := zGroupReader P z₀
  compatible := zGroupReader_compatible P z₀ hx hy

namespace LegGrouping

variable {P : PartitionedTensor (K := K) (A := A) V}

/-- Addresses of `P` assigned to one group. -/
def fiberSupport (G : P.LegGrouping Γ) (γ : Γ) : Finset (BlockAddress A) :=
  P.support.filter fun s ↦ G.group s = γ

/-- Tensor obtained by retaining exactly one group fiber. -/
noncomputable def fiber (G : P.LegGrouping Γ) (γ : Γ) :=
  P.withSupport (G.fiberSupport γ)

/-- Groups whose fiber contains at least one supported address. -/
def occupiedGroups (G : P.LegGrouping Γ) : Finset Γ :=
  Finset.univ.filter fun γ ↦ (G.fiberSupport γ).Nonempty

/-- A group is occupied exactly when its support fiber is nonempty. -/
@[simp] theorem mem_occupiedGroups (G : P.LegGrouping Γ) (γ : Γ) :
    γ ∈ G.occupiedGroups ↔ (G.fiberSupport γ).Nonempty := by
  simp [occupiedGroups]

/-- The support cardinality is the sum of the cardinalities of all group fibers.

Proof sketch: the fibers partition the finite support according to the value of `G.group`; apply
Mathlib's fiberwise cardinality identity with the full finite group set as codomain. -/
theorem card_support_eq_sum_fiber_card (G : P.LegGrouping Γ) :
    P.support.card = ∑ γ : Γ, (G.fiberSupport γ).card := by
  simpa [fiberSupport] using
    (Finset.card_eq_sum_card_fiberwise
      (s := P.support) (t := (Finset.univ : Finset Γ)) (f := G.group)
      (fun _s _hs ↦ Finset.mem_univ _))

/-- Empty fibers may be omitted from the fiberwise support-cardinality sum. -/
theorem card_support_eq_sum_occupied_fiber_card (G : P.LegGrouping Γ) :
    P.support.card = ∑ γ : G.occupiedGroups, (G.fiberSupport γ.1).card := by
  rw [G.card_support_eq_sum_fiber_card]
  calc
    (∑ γ : Γ, (G.fiberSupport γ).card) =
        ∑ γ ∈ G.occupiedGroups, (G.fiberSupport γ).card := by
      symm
      apply Finset.sum_subset (Finset.subset_univ G.occupiedGroups)
      intro γ _hγ hnot
      have hempty : G.fiberSupport γ = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        simpa using hnot
      simp [hempty]
    _ = ∑ γ : G.occupiedGroups, (G.fiberSupport γ.1).card :=
      Finset.sum_subtype G.occupiedGroups (fun _ ↦ Iff.rfl)
        (fun γ ↦ (G.fiberSupport γ).card)

/-- Constant family of the original partitioned ambient leg spaces, one copy per group. -/
abbrev GroupAmbientFamily (_γ : Γ) (c : Leg) := PartitionedSpace K V c

/-- Route every source block into the indexed ambient summand named by its leg-local group. -/
noncomputable def realizeMap (G : P.LegGrouping Γ) : ∀ c,
    PartitionedSpace K V c →ₗ[K]
      IndexedDirectSumSpace K (GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) c := by
  classical
  intro c
  exact ∑ a : A c,
    indexedInclude (K := K)
      (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) (G.blockGroup c a) c ∘ₗ
      DirectSum.lof K (A c) (V c) a ∘ₗ
      DirectSum.component K (A c) (V c) a

omit [Fintype Γ] [DecidableEq Γ] in
/-- On a supported source block, the grouping map is exactly inclusion into the component named
by that address's group.

Proof sketch: only the summand indexed by the source block label survives projection after block
inclusion.  Compatibility rewrites its leg-local group to the address's common group. -/
theorem realizeMap_comp_blockInclude
    (G : P.LegGrouping Γ) (s : BlockAddress A) (hs : s ∈ P.support) (c : Leg) :
    G.realizeMap c ∘ₗ blockInclude (K := K) (V := V) s c =
      indexedInclude (K := K)
        (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) (G.group s) c ∘ₗ
        blockInclude (K := K) (V := V) s c := by
  classical
  ext x
  simp only [realizeMap, LinearMap.sum_apply, LinearMap.comp_apply, blockInclude]
  rw [Finset.sum_eq_single (s c)]
  · rw [G.compatible s hs c]
    simp
  · intro a _ ha
    simp [DirectSum.component.of, Ne.symm ha]
  · simp

/-- The realization restricts to the indexed direct sum of all group-fiber realizations.

Proof sketch: apply `realizeMap` to the support expansion of `P`.  The preceding block lemma
routes each embedded constituent into its group component.  Expanding the target indexed direct
sum gives the same terms, regrouped first by the finite group and then by the filtered support. -/
theorem restricts_groupedIndexedDirectSum (G : P.LegGrouping Γ) :
    Restricts P.realize
      (Tensor.indexedDirectSum
        (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ))
        (fun γ ↦ (G.fiber γ).realize)) := by
  classical
  refine ⟨G.realizeMap, ?_⟩
  let embedded (s : BlockAddress A) :=
    map (blockInclude (K := K) (V := V) s) (P.constituent s)
  have hsource :
      map G.realizeMap P.realize =
        ∑ s ∈ P.support,
          map (indexedInclude (K := K)
            (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) (G.group s))
            (embedded s) := by
    unfold PartitionedTensor.realize realizePartition
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    change map G.realizeMap (embedded s) = _
    calc
      map G.realizeMap (embedded s) =
          map (fun c ↦ G.realizeMap c ∘ₗ blockInclude (K := K) (V := V) s c)
            (P.constituent s) := by rw [map_comp]; rfl
      _ = map (fun c ↦
          indexedInclude (K := K)
            (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) (G.group s) c ∘ₗ
              blockInclude (K := K) (V := V) s c) (P.constituent s) := by
            congr 2
            funext c
            exact G.realizeMap_comp_blockInclude s hs c
      _ = map (indexedInclude (K := K)
            (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) (G.group s))
          (embedded s) := by rw [map_comp]; rfl
  rw [hsource]
  unfold Tensor.indexedDirectSum fiber PartitionedTensor.realize realizePartition
    PartitionedTensor.withSupport fiberSupport
  simp only [map_sum]
  calc
    (∑ s ∈ P.support,
        map (indexedInclude (K := K)
          (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) (G.group s))
          (embedded s)) =
        ∑ γ ∈ (Finset.univ : Finset Γ),
          ∑ s ∈ P.support with G.group s = γ,
            map (indexedInclude (K := K)
              (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) (G.group s))
              (embedded s) :=
      (Finset.sum_fiberwise_of_maps_to
        (s := P.support) (t := Finset.univ) (g := G.group)
        (fun _s _hs ↦ Finset.mem_univ (G.group _s))
        (fun s ↦ map (indexedInclude (K := K)
          (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) (G.group s))
          (embedded s))).symm
    _ = ∑ γ : Γ, ∑ s ∈ P.support with G.group s = γ,
          map (indexedInclude (K := K)
            (V := GroupAmbientFamily (K := K) (V := V) (Γ := Γ)) γ)
            (embedded s) := by
      apply Finset.sum_congr rfl
      intro γ _hγ
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = _ := by rfl

end LegGrouping

end PartitionedTensor

end AlgebraicComplexity.Tensor
