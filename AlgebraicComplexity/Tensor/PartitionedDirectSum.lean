/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.PartitionedExtraction

/-!
# Direct-sum realization of independent partitioned constituents

Variable zeroing first selects a finite support.  To apply an asymptotic sum inequality, the
surviving constituents must then occupy distinct blocks on every tensor leg.  This module proves
that exact interface: legwise injectivity turns a realized partitioned subfamily into a genuine
indexed tensor direct sum by an explicit restriction map.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The selected constituent spaces, indexed by their full block addresses. -/
abbrev SelectedBlockFamily (selected : Finset (BlockAddress A))
    (s : selected) (c : Leg) := V c (s.1 c)

/-- No two selected addresses use the same block label on any tensor leg. -/
def IsLegwiseInjective (selected : Finset (BlockAddress A)) : Prop :=
  ∀ c, Set.InjOn (fun s : BlockAddress A => s c) (selected : Set (BlockAddress A))

/-- On each leg, project the partitioned ambient space to the blocks used by the selected
addresses and reindex them by those addresses. -/
noncomputable def partitionToSelectedMap (selected : Finset (BlockAddress A)) : ∀ c,
    PartitionedSpace K V c →ₗ[K]
      IndexedDirectSumSpace K (SelectedBlockFamily (V := V) selected) c := by
  classical
  exact fun c => ∑ s : selected,
    indexedInclude (K := K) (V := SelectedBlockFamily (V := V) selected) s c ∘ₗ
      DirectSum.component K (A c) (V c) (s.1 c)

omit [∀ c, Fintype (A c)] in
theorem partitionToSelectedMap_comp_blockInclude
    (selected : Finset (BlockAddress A)) (hinj : IsLegwiseInjective selected)
    (s : BlockAddress A) (hs : s ∈ selected) (c : Leg) :
    partitionToSelectedMap (K := K) (V := V) selected c ∘ₗ
        blockInclude (K := K) (V := V) s c =
      indexedInclude (K := K) (V := SelectedBlockFamily (V := V) selected) ⟨s, hs⟩ c := by
  classical
  ext x
  simp only [LinearMap.comp_apply, partitionToSelectedMap, LinearMap.sum_apply,
    blockInclude, indexedInclude]
  rw [Finset.sum_eq_single ⟨s, hs⟩]
  · simp
  · intro t _ hts
    have hlabel : s c ≠ t.1 c := by
      intro hlabelEq
      have haddress : t.1 = s := hinj c t.2 hs hlabelEq.symm
      exact hts (Subtype.ext haddress)
    simp [DirectSum.component.of, hlabel]
  · simp

omit [∀ c, Fintype (A c)] in
/-- The explicit projection maps the selected partitioned realization to the indexed direct sum
of precisely its constituents. -/
theorem map_partitionToSelectedMap_realizePartition
    (selected : Finset (BlockAddress A)) (hinj : IsLegwiseInjective selected)
    (constituent : ∀ s : BlockAddress A, Tensor3 K (fun c => V c (s c))) :
    map (partitionToSelectedMap (K := K) (V := V) selected)
        (realizePartition selected constituent) =
      indexedDirectSum (V := SelectedBlockFamily (V := V) selected)
        (fun s : selected => constituent s.1) := by
  classical
  unfold realizePartition
  rw [map_sum]
  have hterm (s : BlockAddress A) (hs : s ∈ selected) :
      map (partitionToSelectedMap (K := K) (V := V) selected)
          (map (blockInclude (K := K) (V := V) s) (constituent s)) =
        map (indexedInclude (K := K) (V := SelectedBlockFamily (V := V) selected) ⟨s, hs⟩)
          (constituent s) := by
    calc
      map (partitionToSelectedMap (K := K) (V := V) selected)
          (map (blockInclude (K := K) (V := V) s) (constituent s)) =
          map (fun c => partitionToSelectedMap (K := K) (V := V) selected c ∘ₗ
            blockInclude (K := K) (V := V) s c) (constituent s) := by
              rw [map_comp]
              rfl
      _ = map (indexedInclude (K := K)
            (V := SelectedBlockFamily (V := V) selected) ⟨s, hs⟩) (constituent s) := by
        congr 2
        funext c
        exact partitionToSelectedMap_comp_blockInclude selected hinj s hs c
  unfold indexedDirectSum
  let f : BlockAddress A →
      Tensor3 K (IndexedDirectSumSpace K (SelectedBlockFamily (V := V) selected)) :=
    fun s => if hs : s ∈ selected then
      map (indexedInclude (K := K)
        (V := SelectedBlockFamily (V := V) selected) ⟨s, hs⟩) (constituent s)
    else 0
  calc
    _ = ∑ s ∈ selected, f s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hterm s hs]
      simp [f, hs]
    _ = ∑ s : selected, f s :=
      Finset.sum_subtype selected (fun _ => Iff.rfl) f
    _ = ∑ s : selected,
        map (indexedInclude (K := K)
          (V := SelectedBlockFamily (V := V) selected) s) (constituent s.1) := by
      apply Finset.sum_congr rfl
      intro s _
      simp [f, s.2]

namespace Restricts

/-- A partitioned tensor with legwise-independent support restricts to the genuine indexed direct
sum of its constituents. -/
theorem partitionedLegwiseInjective_to_indexedDirectSum
    (P : PartitionedTensor (K := K) (A := A) V)
    (hinj : IsLegwiseInjective P.support) :
    Restricts P.realize
      (Tensor.indexedDirectSum (V := SelectedBlockFamily (V := V) P.support)
        (fun s : P.support => P.constituent s.1)) :=
  ⟨partitionToSelectedMap (K := K) (V := V) P.support,
    map_partitionToSelectedMap_realizePartition P.support hinj P.constituent⟩

end Restricts

end AlgebraicComplexity.Tensor
