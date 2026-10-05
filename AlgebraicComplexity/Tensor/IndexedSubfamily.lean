/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum

/-!
# Subfamilies of finite indexed tensor direct sums

A type-selection argument first distributes a tensor power into independent word blocks and then
keeps only the words of one multiplicity type.  This file implements the second operation for an
arbitrary finite indexed tensor family.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w

variable {K : Type u} [CommSemiring K]
variable {I : Type w} [Fintype I]
variable {V : I → Leg → Type v}
variable [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)]

/-- The family obtained by restricting an indexed family to a finite set of indices. -/
abbrev IndexedSubfamily (s : Finset I) (i : s) : Leg → Type v := V i.1

/-- On every leg, discard all direct-sum blocks outside `s` and retain the blocks in `s`. -/
noncomputable def indexedSelectMap (s : Finset I) : ∀ c,
    IndexedDirectSumSpace K V c →ₗ[K]
      IndexedDirectSumSpace K (IndexedSubfamily (V := V) s) c := by
  classical
  exact fun c ↦ DirectSum.toModule K I _ fun i ↦
    if hi : i ∈ s then
      DirectSum.lof K s (fun j ↦ V j.1 c) ⟨i, hi⟩
    else 0

omit [Fintype I] in
theorem indexedSelectMap_comp_include_of_mem (s : Finset I) (i : I)
    (hi : i ∈ s) (c : Leg) :
    indexedSelectMap (K := K) (V := V) s c ∘ₗ
        indexedInclude (K := K) (V := V) i c =
      indexedInclude (K := K) (V := IndexedSubfamily (V := V) s) ⟨i, hi⟩ c := by
  classical
  ext x
  simp only [LinearMap.comp_apply, indexedSelectMap, indexedInclude,
    DirectSum.toModule_lof]
  rw [dif_pos hi]
  congr
  apply Subsingleton.elim

omit [Fintype I] in
theorem indexedSelectMap_comp_include_of_not_mem (s : Finset I) (i : I)
    (hi : i ∉ s) (c : Leg) :
    indexedSelectMap (K := K) (V := V) s c ∘ₗ
        indexedInclude (K := K) (V := V) i c = 0 := by
  classical
  ext x
  simp [indexedSelectMap, indexedInclude, hi]

/-- Selecting a subfamily carries the full indexed tensor direct sum to precisely the direct sum
over the selected subtype. -/
theorem map_indexedSelectMap_indexedDirectSum
    (T : ∀ i, Tensor3 K (V i)) (s : Finset I) :
    map (indexedSelectMap (K := K) (V := V) s) (indexedDirectSum T) =
      indexedDirectSum (V := IndexedSubfamily (V := V) s) (fun i : s ↦ T i.1) := by
  classical
  unfold indexedDirectSum
  rw [map_sum]
  have hterm (i : I) :
      map (indexedSelectMap (K := K) (V := V) s)
          (map (indexedInclude (K := K) (V := V) i) (T i)) =
        if hi : i ∈ s then
          map (indexedInclude (K := K) (V := IndexedSubfamily (V := V) s) ⟨i, hi⟩) (T i)
        else 0 := by
    split_ifs with hi
    · calc
        map (indexedSelectMap (K := K) (V := V) s)
              (map (indexedInclude (K := K) (V := V) i) (T i)) =
            map (fun c ↦ indexedSelectMap (K := K) (V := V) s c ∘ₗ
              indexedInclude (K := K) (V := V) i c) (T i) := by
                rw [map_comp]
                rfl
        _ = map (indexedInclude (K := K)
              (V := IndexedSubfamily (V := V) s) ⟨i, hi⟩) (T i) := by
          congr 2
          funext c
          exact indexedSelectMap_comp_include_of_mem (K := K) (V := V) s i hi c
    · calc
        map (indexedSelectMap (K := K) (V := V) s)
              (map (indexedInclude (K := K) (V := V) i) (T i)) =
            map (fun c ↦ indexedSelectMap (K := K) (V := V) s c ∘ₗ
              indexedInclude (K := K) (V := V) i c) (T i) := by
                rw [map_comp]
                rfl
        _ = 0 := by
          apply map_eq_zero_of_coord _ (T i) .X
          exact indexedSelectMap_comp_include_of_not_mem (K := K) (V := V) s i hi .X
  simp_rw [hterm]
  let g : s → Tensor3 K (IndexedDirectSumSpace K (IndexedSubfamily (V := V) s)) :=
    fun i ↦ map (indexedInclude (K := K) (V := IndexedSubfamily (V := V) s) i) (T i.1)
  let f : I → Tensor3 K (IndexedDirectSumSpace K (IndexedSubfamily (V := V) s)) :=
    fun i ↦ if hi : i ∈ s then g ⟨i, hi⟩ else 0
  change (∑ i : I, if hi : i ∈ s then g ⟨i, hi⟩ else 0) = ∑ i : s, g i
  calc
    (∑ i : I, if hi : i ∈ s then g ⟨i, hi⟩ else 0) =
        ∑ i : I, if i ∈ s then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [f, hi]
    _ = ∑ i ∈ s, f i := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ i : s, f i :=
      Finset.sum_subtype s (fun _ ↦ Iff.rfl) f
    _ = ∑ i : s, g i := by
      apply Finset.sum_congr rfl
      intro i _
      simp [f, i.2]

namespace Restricts

/-- A finite indexed tensor direct sum restricts to the direct sum of any finite subfamily. -/
theorem indexedDirectSum_subfamily (T : ∀ i, Tensor3 K (V i)) (s : Finset I) :
    Restricts (Tensor.indexedDirectSum T)
      (Tensor.indexedDirectSum (V := IndexedSubfamily (V := V) s)
        (fun i : s ↦ T i.1)) :=
  ⟨indexedSelectMap (K := K) (V := V) s,
    map_indexedSelectMap_indexedDirectSum T s⟩

end Restricts

end AlgebraicComplexity.Tensor
