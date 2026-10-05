/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.BorderRank
import Mathlib.Algebra.DirectSum.Module

/-!
# Finite indexed direct sums of tensors

Laser-method constructions produce finite families of independent tensors, often with different
ambient spaces. This module embeds each member into the corresponding module direct sum on every
leg and adds the embedded tensors. It proves the structural maps, restriction and isomorphism
calculus, rank bounds, and the canonical identification of a one-element indexed sum with its
single summand. It complements the lightweight binary product representation in
`Tensor.DirectSum`.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι]
variable {V : ι → Leg → Type v}
variable [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)]
variable {W : ι → Leg → Type x}
variable [∀ i c, AddCommMonoid (W i c)] [∀ i c, Module K (W i c)]

/-- Ambient leg spaces for an indexed direct sum of tensors. -/
abbrev IndexedDirectSumSpace (K : Type u) [CommSemiring K]
    (V : ι → Leg → Type v)
    [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)] (c : Leg) :=
  ⨁ i, V i c

/-- Include one indexed summand on each tensor leg. -/
noncomputable def indexedInclude (i : ι) :
    ∀ c, V i c →ₗ[K] IndexedDirectSumSpace K V c :=
  by
    classical
    exact fun c ↦ DirectSum.lof K ι (fun j ↦ V j c) i

/-- The equivalence of indexed direct sums induced componentwise by linear equivalences. -/
noncomputable def indexedEquiv (f : ∀ i c, V i c ≃ₗ[K] W i c) :
    ∀ c, IndexedDirectSumSpace K V c ≃ₗ[K] IndexedDirectSumSpace K W c :=
  fun c ↦ DFinsupp.mapRange.linearEquiv (fun i ↦ f i c)

/-- The map on indexed direct sums induced componentwise by linear maps. -/
def indexedMap (f : ∀ i c, V i c →ₗ[K] W i c) :
    ∀ c, IndexedDirectSumSpace K V c →ₗ[K] IndexedDirectSumSpace K W c :=
  fun c ↦ DirectSum.lmap (fun i ↦ f i c)

/-- The family of factorwise tensor products of two indexed families. -/
abbrev IndexedExternalFamily
    (i : ι) (c : Leg) :=
  TensorProduct K (V i c) (W i c)

/-- On every leg, project a tensor product of two indexed direct sums onto its diagonal blocks.
The `(i,j)` block is killed unless `i = j`, and the surviving `(i,i)` block is included in the
`i`th output summand. -/
noncomputable def indexedDiagonalMap : ∀ c,
    TensorProduct K (IndexedDirectSumSpace K V c) (IndexedDirectSumSpace K W c) →ₗ[K]
      IndexedDirectSumSpace K
        (IndexedExternalFamily (K := K) (V := V) (W := W)) c := by
  classical
  exact fun c ↦ ∑ i,
    DirectSum.lof K ι (fun j ↦ TensorProduct K (V j c) (W j c)) i ∘ₗ
      TensorProduct.map
        (DirectSum.component K ι (fun j ↦ V j c) i)
        (DirectSum.component K ι (fun j ↦ W j c) i)

theorem indexedDiagonalMap_comp_includes_same (i : ι) (c : Leg) :
    indexedDiagonalMap (K := K) (V := V) (W := W) c ∘ₗ
        TensorProduct.map
          (indexedInclude (K := K) (V := V) i c)
          (indexedInclude (K := K) (V := W) i c) =
      indexedInclude (K := K)
        (V := IndexedExternalFamily (K := K) (V := V) (W := W)) i c := by
  classical
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, indexedDiagonalMap,
    LinearMap.sum_apply, indexedInclude]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [DirectSum.component.of, Ne.symm hji]
  · simp

theorem indexedDiagonalMap_comp_includes_of_ne {i j : ι} (hij : i ≠ j) (c : Leg) :
    indexedDiagonalMap (K := K) (V := V) (W := W) c ∘ₗ
        TensorProduct.map
          (indexedInclude (K := K) (V := V) i c)
          (indexedInclude (K := K) (V := W) j c) = 0 := by
  classical
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, indexedDiagonalMap,
    LinearMap.sum_apply, indexedInclude, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : i = k
  · subst k
    simp [DirectSum.component.of, Ne.symm hij]
  · simp [DirectSum.component.of, hki]

/-- The diagonal map carries the external product of two copies of the same embedded block to the
corresponding embedded external product. -/
theorem map_indexedDiagonalMap_external_includes_same (i : ι)
    (T : Tensor3 K (V i)) (S : Tensor3 K (W i)) :
    map (indexedDiagonalMap (K := K) (V := V) (W := W))
        (external
          (map (indexedInclude (K := K) (V := V) i) T)
          (map (indexedInclude (K := K) (V := W) i) S)) =
      map (indexedInclude (K := K)
        (V := IndexedExternalFamily (K := K) (V := V) (W := W)) i)
        (external T S) := by
  rw [← map_external]
  calc
    map (indexedDiagonalMap (K := K) (V := V) (W := W))
        (map (fun c ↦ TensorProduct.map
          (indexedInclude (K := K) (V := V) i c)
          (indexedInclude (K := K) (V := W) i c)) (external T S)) =
      map (fun c ↦ indexedDiagonalMap (K := K) (V := V) (W := W) c ∘ₗ
        TensorProduct.map
          (indexedInclude (K := K) (V := V) i c)
          (indexedInclude (K := K) (V := W) i c)) (external T S) := by
        rw [map_comp]
        rfl
    _ = map (indexedInclude (K := K)
          (V := IndexedExternalFamily (K := K) (V := V) (W := W)) i)
        (external T S) := by
      congr 2
      funext c
      exact indexedDiagonalMap_comp_includes_same (K := K) (V := V) (W := W) i c

/-- Cross terms from differently indexed embedded blocks are killed by the diagonal map. -/
theorem map_indexedDiagonalMap_external_includes_of_ne {i j : ι} (hij : i ≠ j)
    (T : Tensor3 K (V i)) (S : Tensor3 K (W j)) :
    map (indexedDiagonalMap (K := K) (V := V) (W := W))
        (external
          (map (indexedInclude (K := K) (V := V) i) T)
          (map (indexedInclude (K := K) (V := W) j) S)) = 0 := by
  rw [← map_external]
  calc
    map (indexedDiagonalMap (K := K) (V := V) (W := W))
        (map (fun c ↦ TensorProduct.map
          (indexedInclude (K := K) (V := V) i c)
          (indexedInclude (K := K) (V := W) j c)) (external T S)) =
      map (fun c ↦ indexedDiagonalMap (K := K) (V := V) (W := W) c ∘ₗ
        TensorProduct.map
          (indexedInclude (K := K) (V := V) i c)
          (indexedInclude (K := K) (V := W) j c)) (external T S) := by
        rw [map_comp]
        rfl
    _ = 0 := by
      apply map_eq_zero_of_coord _ (external T S) .X
      exact indexedDiagonalMap_comp_includes_of_ne
        (K := K) (V := V) (W := W) hij .X

/-- A finite direct sum of tensors with possibly different leg spaces. -/
noncomputable def indexedDirectSum (T : ∀ i, Tensor3 K (V i)) :
    Tensor3 K (IndexedDirectSumSpace K V) :=
  ∑ i, map (indexedInclude (K := K) (V := V) i) (T i)

/-- Fold an indexed direct-sum space into a common target space, using a possibly different
linear map on every summand. -/
noncomputable def indexedFoldMap
    {U : Leg → Type*} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (f : ∀ i c, V i c →ₗ[K] U c) :
    ∀ c, IndexedDirectSumSpace K V c →ₗ[K] U c := by
  classical
  exact fun c ↦ DirectSum.toModule K ι (U c) fun i ↦ f i c

omit [Fintype ι] in
/-- Folding after inclusion applies the map assigned to that summand. -/
theorem indexedFoldMap_comp_indexedInclude
    {U : Leg → Type*} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (f : ∀ i c, V i c →ₗ[K] U c) (i : ι) (c : Leg) :
    indexedFoldMap (K := K) (V := V) f c ∘ₗ indexedInclude (K := K) (V := V) i c =
      f i c := by
  ext x
  simp [indexedFoldMap, indexedInclude]

/-- Folding an indexed tensor direct sum is the ordinary sum of the componentwise images. -/
theorem map_indexedFoldMap_indexedDirectSum
    {U : Leg → Type*} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (f : ∀ i c, V i c →ₗ[K] U c) (T : ∀ i, Tensor3 K (V i)) :
    map (indexedFoldMap (K := K) (V := V) f) (indexedDirectSum T) =
      ∑ i, map (f i) (T i) := by
  classical
  unfold indexedDirectSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    map (indexedFoldMap (K := K) (V := V) f)
        (map (indexedInclude (K := K) (V := V) i) (T i)) =
      map (fun c ↦ indexedFoldMap (K := K) (V := V) f c ∘ₗ
        indexedInclude (K := K) (V := V) i c) (T i) := by
        rw [map_comp]
        rfl
    _ = map (f i) (T i) := by
      congr 2
      funext c
      exact indexedFoldMap_comp_indexedInclude f i c

/-- Permuting tensor legs commutes with a finite indexed direct sum. -/
theorem permute_indexedDirectSum (e : Orientation) (T : ∀ i, Tensor3 K (V i)) :
    permute e (indexedDirectSum T) =
      indexedDirectSum (V := fun i c => V i (e.symm c))
        (fun i => permute e (T i)) := by
  classical
  unfold indexedDirectSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (PiTensorProduct.map_reindex
    (indexedInclude (K := K) (V := V) i) e (T i)).symm

/-- The external product of two indexed direct sums restricts, by killing all cross terms, to the
indexed direct sum of the componentwise external products. -/
theorem map_indexedDiagonalMap_external_indexedDirectSum
    (T : ∀ i, Tensor3 K (V i)) (S : ∀ i, Tensor3 K (W i)) :
    map (indexedDiagonalMap (K := K) (V := V) (W := W))
        (external (indexedDirectSum T) (indexedDirectSum S)) =
      indexedDirectSum (fun i ↦ external (T i) (S i)) := by
  classical
  unfold indexedDirectSum
  rw [external_sum_sum, map_sum]
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact map_indexedDiagonalMap_external_includes_same
      (K := K) (V := V) (W := W) i (T i) (S i)
  · intro j _ hji
    exact map_indexedDiagonalMap_external_includes_of_ne
      (K := K) (V := V) (W := W) (Ne.symm hji) (T i) (S j)
  · simp

namespace Restricts

/-- Relation-level form of diagonal extraction for indexed direct sums. -/
theorem external_indexedDirectSum_diagonal
    (T : ∀ i, Tensor3 K (V i)) (S : ∀ i, Tensor3 K (W i)) :
    Restricts (Tensor.external (indexedDirectSum T) (indexedDirectSum S))
      (indexedDirectSum (fun i ↦ Tensor.external (T i) (S i))) :=
  ⟨indexedDiagonalMap (K := K) (V := V) (W := W),
    map_indexedDiagonalMap_external_indexedDirectSum T S⟩

/-- Three-factor diagonal extraction, obtained by applying the binary construction twice. -/
theorem external3_indexedDirectSum_diagonal
    {U : ι → Leg → Type*}
    [∀ i c, AddCommMonoid (U i c)] [∀ i c, Module K (U i c)]
    (T : ∀ i, Tensor3 K (V i)) (S : ∀ i, Tensor3 K (W i))
    (R : ∀ i, Tensor3 K (U i)) :
    Restricts
      (Tensor.external
        (Tensor.external (indexedDirectSum T) (indexedDirectSum S))
        (indexedDirectSum R))
      (indexedDirectSum (fun i ↦ Tensor.external (Tensor.external (T i) (S i)) (R i))) := by
  let TS : ι → Leg → Type _ :=
    IndexedExternalFamily (K := K) (V := V) (W := W)
  have hTS : Restricts
      (Tensor.external (indexedDirectSum T) (indexedDirectSum S))
      (indexedDirectSum (fun i ↦ Tensor.external (T i) (S i))) :=
    external_indexedDirectSum_diagonal T S
  have hfirst := hTS.external (Restricts.refl (indexedDirectSum R))
  exact hfirst.trans
    (external_indexedDirectSum_diagonal
      (V := TS) (W := U)
      (fun i ↦ Tensor.external (T i) (S i)) R)

/-- The cyclic three-orientation product of an indexed direct sum restricts to the indexed direct
sum of the componentwise cyclic products.

Proof sketch: leg permutation commutes with indexed direct sums.  After rewriting the two
permuted factors in that form, apply the three-factor diagonal map, which retains only triples
whose three indices agree. -/
theorem cyclic_indexedDirectSum_diagonal (T : ∀ i, Tensor3 K (V i)) :
    Restricts
      (Tensor.external
        (Tensor.external (indexedDirectSum T)
          (Tensor.permute cycle (indexedDirectSum T)))
        (Tensor.permute cycle.symm (indexedDirectSum T)))
      (indexedDirectSum (fun i ↦
        Tensor.external
          (Tensor.external (T i) (Tensor.permute cycle (T i)))
          (Tensor.permute cycle.symm (T i)))) := by
  rw [Tensor.permute_indexedDirectSum, Tensor.permute_indexedDirectSum]
  exact external3_indexedDirectSum_diagonal T
    (fun i ↦ Tensor.permute cycle (T i))
    (fun i ↦ Tensor.permute cycle.symm (T i))

end Restricts

/-- Componentwise maps commute with finite indexed tensor direct sums. -/
theorem map_indexedDirectSum (f : ∀ i c, V i c →ₗ[K] W i c)
    (T : ∀ i, Tensor3 K (V i)) :
    map (indexedMap f) (indexedDirectSum T) =
      indexedDirectSum (fun i ↦ map (f i) (T i)) := by
  classical
  unfold indexedDirectSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    map (indexedMap f) (map (indexedInclude (K := K) (V := V) i) (T i)) =
        map (fun c ↦ indexedMap f c ∘ₗ indexedInclude (K := K) (V := V) i c) (T i) := by
          rw [map_comp]
          rfl
    _ = map (fun c ↦ indexedInclude (K := K) (V := W) i c ∘ₗ f i c) (T i) := by
          congr 2
          funext c
          ext x
          simp [indexedMap, indexedInclude]
    _ = map (indexedInclude (K := K) (V := W) i) (map (f i) (T i)) := by
          rw [map_comp]
          rfl

/-- Componentwise equivalences carry an indexed tensor direct sum to the indexed direct sum of
the transported components. -/
theorem map_indexedEquiv_indexedDirectSum (f : ∀ i c, V i c ≃ₗ[K] W i c)
    (T : ∀ i, Tensor3 K (V i)) :
    map (fun c ↦ (indexedEquiv f c).toLinearMap) (indexedDirectSum T) =
      indexedDirectSum (fun i ↦ map (fun c ↦ (f i c).toLinearMap) (T i)) := by
  exact map_indexedDirectSum (fun i c ↦ (f i c).toLinearMap) T

/-! ## Flattening dependent finite sums -/

section Sigma

variable [DecidableEq ι]
variable {J : ι → Type*} [∀ i, Fintype (J i)]
variable {S : ∀ i, J i → Leg → Type*}
variable [∀ i j c, AddCommMonoid (S i j c)] [∀ i j c, Module K (S i j c)]

/-- The canonical legwise equivalence between a direct sum indexed by a dependent pair and the
corresponding iterated direct sum. -/
noncomputable def indexedSigmaCurryEquiv : ∀ c,
    IndexedDirectSumSpace K (fun ij : Σ i, J i ↦ S ij.1 ij.2) c ≃ₗ[K]
      IndexedDirectSumSpace K
        (fun i c ↦ IndexedDirectSumSpace K (fun j : J i ↦ S i j) c) c := by
  classical
  intro c
  exact DirectSum.sigmaLcurryEquiv K
    (ι := ι) (α := J) (δ := fun i j ↦ S i j c)

/- Evaluating the curried dependent direct sum at `(i,j)` reads the original dependent-pair
coordinate `⟨i,j⟩`. -/
omit [Fintype ι] [∀ i, Fintype (J i)] in
private theorem indexedSigmaCurryEquiv_apply (c : Leg)
    (f : IndexedDirectSumSpace K (fun ij : Σ i, J i ↦ S ij.1 ij.2) c)
    (i : ι) (j : J i) :
    indexedSigmaCurryEquiv (K := K) (S := S) c f i j = f ⟨i, j⟩ := by
  rfl

/-- Flattening or currying a dependent finite indexed direct sum does not change its tensor.

This is the associativity law needed by recursive extraction and hole repair: an outer direct
sum of inner direct sums is canonically isomorphic to one direct sum over the dependent-pair
index. -/
theorem map_indexedSigmaCurryEquiv_indexedDirectSum
    (T : ∀ ij : Σ i, J i, Tensor3 K (S ij.1 ij.2)) :
    map (fun c ↦ (indexedSigmaCurryEquiv (K := K) (S := S) c).toLinearMap)
        (indexedDirectSum T) =
      indexedDirectSum (fun i ↦ indexedDirectSum (fun j : J i ↦ T ⟨i, j⟩)) := by
  classical
  unfold indexedDirectSum
  rw [map_sum]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  calc
    map (fun c ↦ (indexedSigmaCurryEquiv (K := K) (S := S) c).toLinearMap)
        (map (indexedInclude (K := K)
          (V := fun ij : Σ i, J i ↦ S ij.1 ij.2) ⟨i, j⟩) (T ⟨i, j⟩)) =
      map (fun c ↦
        (indexedSigmaCurryEquiv (K := K) (S := S) c).toLinearMap ∘ₗ
          indexedInclude (K := K)
            (V := fun ij : Σ i, J i ↦ S ij.1 ij.2) ⟨i, j⟩ c) (T ⟨i, j⟩) := by
        rw [map_comp]
        rfl
    _ = map (fun c ↦
        indexedInclude (K := K)
            (V := fun i c ↦ IndexedDirectSumSpace K (fun j : J i ↦ S i j) c) i c ∘ₗ
          indexedInclude (K := K) (V := fun j : J i ↦ S i j) j c) (T ⟨i, j⟩) := by
        congr 2
        funext c
        ext x k j'
        simp only [LinearMap.comp_apply, indexedInclude,
          LinearEquiv.coe_toLinearMap, indexedSigmaCurryEquiv_apply]
        by_cases hk : i = k
        · subst k
          simp [DirectSum.lof_eq_of, DirectSum.of_apply]
          split_ifs with hj
          · subst j'
            rfl
          · rfl
        · have hsigma : (⟨i, j⟩ : Σ i, J i) ≠ ⟨k, j'⟩ := by
            intro h
            exact hk (congrArg Sigma.fst h)
          simp [DirectSum.lof_eq_of, DirectSum.of_apply, hk, hsigma]
    _ = map (indexedInclude (K := K)
          (V := fun i c ↦ IndexedDirectSumSpace K (fun j : J i ↦ S i j) c) i)
        (map (indexedInclude (K := K) (V := fun j : J i ↦ S i j) j)
          (T ⟨i, j⟩)) := by
        rw [map_comp]
        rfl

/-- Relation-facing form of dependent-sum flattening. -/
theorem Restricts.indexedDirectSum_sigma
    (T : ∀ ij : Σ i, J i, Tensor3 K (S ij.1 ij.2)) :
    Restricts (indexedDirectSum T)
      (indexedDirectSum (fun i ↦ indexedDirectSum (fun j : J i ↦ T ⟨i, j⟩))) := by
  exact ⟨fun c ↦ (indexedSigmaCurryEquiv (K := K) (S := S) c).toLinearMap,
    map_indexedSigmaCurryEquiv_indexedDirectSum T⟩

/-- A dependent-pair indexed direct sum is canonically isomorphic to the corresponding nested
indexed direct sum.

This strengthens `Restricts.indexedDirectSum_sigma` to the semantic statement supplied by the
linear equivalence `indexedSigmaCurryEquiv`.  Extraction clients can therefore flatten a nested
family, reindex the resulting sigma type by its cardinality, and present the result as `Fin n`
identical copies without losing information in either direction.

Proof sketch: use `indexedSigmaCurryEquiv` independently on the three tensor legs; the preceding
map theorem computes its action on the direct-sum tensor. -/
theorem Isomorphic.indexedDirectSum_sigma
    (T : ∀ ij : Σ i, J i, Tensor3 K (S ij.1 ij.2)) :
    Isomorphic (indexedDirectSum T)
      (indexedDirectSum (fun i ↦ indexedDirectSum (fun j : J i ↦ T ⟨i, j⟩))) := by
  exact ⟨fun c ↦ indexedSigmaCurryEquiv (K := K) (S := S) c,
    map_indexedSigmaCurryEquiv_indexedDirectSum T⟩

end Sigma

/-- The indexed direct sum over an empty type is zero. -/
@[simp] theorem indexedDirectSum_isEmpty [IsEmpty ι] (T : ∀ i, Tensor3 K (V i)) :
    indexedDirectSum T = 0 := by
  classical
  simp [indexedDirectSum]

namespace Restricts

/-- Exact restrictions can be applied independently to all indexed direct summands. -/
theorem indexedDirectSum {T : ∀ i, Tensor3 K (V i)} {S : ∀ i, Tensor3 K (W i)}
    (h : ∀ _i, Restricts (T _i) (S _i)) :
    Restricts (Tensor.indexedDirectSum T) (Tensor.indexedDirectSum S) := by
  classical
  choose f hf using h
  refine ⟨indexedMap f, ?_⟩
  rw [map_indexedDirectSum]
  simp_rw [hf]

/-- Reindex a finite family of tensor restrictions along an equivalence of its index types.

Unlike `indexedDirectSum_const_equiv`, the summands may vary with the index.  This is the
paper-independent adapter needed when a flat collection of damaged tensors is reorganized into
the dependent occurrence tree of a hole-repair certificate. -/
theorem indexedDirectSum_equiv
    {J : Type*} [Fintype J]
    {U : J → Leg → Type*}
    [∀ j c, AddCommMonoid (U j c)] [∀ j c, Module K (U j c)]
    (e : ι ≃ J)
    {T : ∀ i, Tensor3 K (V i)} {S : ∀ j, Tensor3 K (U j)}
    (h : ∀ i, Restricts (T i) (S (e i))) :
    Restricts (Tensor.indexedDirectSum T) (Tensor.indexedDirectSum S) := by
  classical
  choose componentMap hcomponentMap using h
  let foldedMap : ∀ i c, V i c →ₗ[K] IndexedDirectSumSpace K U c :=
    fun i c ↦ indexedInclude (K := K) (V := U) (e i) c ∘ₗ componentMap i c
  refine ⟨indexedFoldMap (K := K) (V := V) foldedMap, ?_⟩
  rw [map_indexedFoldMap_indexedDirectSum]
  calc
    (∑ i, map (foldedMap i) (T i)) =
        ∑ i, map (indexedInclude (K := K) (V := U) (e i)) (S (e i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp only [foldedMap]
      calc
        map (fun c ↦ indexedInclude (K := K) (V := U) (e i) c ∘ₗ
            componentMap i c) (T i) =
            map (indexedInclude (K := K) (V := U) (e i))
              (map (componentMap i) (T i)) := by
          rw [map_comp]
          rfl
        _ = map (indexedInclude (K := K) (V := U) (e i)) (S (e i)) := by
          rw [hcomponentMap i]
    _ = ∑ j, map (indexedInclude (K := K) (V := U) j) (S j) := by
      exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = Tensor.indexedDirectSum S := by
      rfl

/-- Independent restrictions from indexed summands into one common ambient space fold the source
direct sum into the ordinary sum of their targets. -/
theorem indexedDirectSum_to_sum
    {U : Leg → Type*} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    {T : ∀ _i, Tensor3 K (V _i)} {S : ∀ _i, Tensor3 K U}
    (h : ∀ _i, Restricts (T _i) (S _i)) :
    Restricts (Tensor.indexedDirectSum T) (∑ i, S i) := by
  classical
  choose f hf using h
  refine ⟨indexedFoldMap (K := K) (V := V) f, ?_⟩
  rw [map_indexedFoldMap_indexedDirectSum]
  simp_rw [hf]

/-- Reindexing a finite direct sum of identical tensors along an equivalence is an exact
restriction (indeed, an isomorphism).  This constant-family form avoids all dependent transports
and is the natural adapter from a numerical copy count to a structured recursive index. -/
theorem indexedDirectSum_const_equiv
    {J : Type*} [Fintype J]
    {U : Leg → Type*} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (e : ι ≃ J) (T : Tensor3 K U) :
    Restricts
      (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) (fun _ ↦ T))
      (Tensor.indexedDirectSum (V := fun _ : J ↦ U) (fun _ ↦ T)) := by
  classical
  let f : ∀ i : ι, ∀ c, U c →ₗ[K] IndexedDirectSumSpace K (fun _ : J ↦ U) c :=
    fun i ↦ indexedInclude (K := K) (V := fun _ : J ↦ U) (e i)
  refine ⟨indexedFoldMap (K := K) (V := fun _ : ι ↦ U) f, ?_⟩
  rw [map_indexedFoldMap_indexedDirectSum]
  unfold Tensor.indexedDirectSum
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

end Restricts

namespace Isomorphic

/-- Isomorphisms can be applied independently to every indexed direct summand. -/
theorem indexedDirectSum {T : ∀ i, Tensor3 K (V i)} {S : ∀ i, Tensor3 K (W i)}
    (h : ∀ i, Isomorphic (T i) (S i)) :
    Isomorphic (Tensor.indexedDirectSum T) (Tensor.indexedDirectSum S) := by
  classical
  choose f hf using h
  refine ⟨indexedEquiv f, ?_⟩
  change Tensor.map (fun c ↦ (indexedEquiv f c).toLinearMap)
    (Tensor.indexedDirectSum T) = _
  rw [map_indexedEquiv_indexedDirectSum]
  congr 1
  funext i
  simpa [PiTensorProduct.congr] using hf i

section Unique

variable [Unique ι]
variable {U : Leg → Type v}
variable [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]

/-- On each leg, a direct sum indexed by a one-element type is its single summand. -/
private noncomputable def uniqueDirectSumEquiv (c : Leg) :
    IndexedDirectSumSpace K (fun _ : ι ↦ U) c ≃ₗ[K] U c :=
  (DirectSum.linearEquivFunOnFintype K ι (fun _ : ι ↦ U c)).trans
    (LinearEquiv.funUnique ι K (U c))

/-- **A direct sum of one copy is that copy.**  For a one-element index type, the indexed direct
sum of the constant family at `T` is legwise isomorphic to `T` itself.

Proof sketch: the sum over a `Unique` index type collapses to its single term, and on each leg the
composite of the canonical inclusion with `uniqueDirectSumEquiv` is the identity. -/
theorem indexedDirectSum_unique (T : Tensor3 K U) :
    Isomorphic (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) (fun _ ↦ T)) T := by
  classical
  refine ⟨uniqueDirectSumEquiv (K := K) (ι := ι) (U := U), ?_⟩
  show Tensor.map
      (fun c ↦ (uniqueDirectSumEquiv (K := K) (ι := ι) (U := U) c).toLinearMap)
      (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) (fun _ ↦ T)) = T
  unfold Tensor.indexedDirectSum
  rw [Fintype.sum_unique]
  have hleg :
      (fun c ↦ (uniqueDirectSumEquiv (K := K) (ι := ι) (U := U) c).toLinearMap ∘ₗ
        Tensor.indexedInclude (K := K) (V := fun _ : ι ↦ U) (default : ι) c) =
        fun c ↦ LinearMap.id (R := K) (M := U c) := by
    funext c
    refine LinearMap.ext fun x ↦ ?_
    simp [uniqueDirectSumEquiv, Tensor.indexedInclude]
  have hcomp :
      Tensor.map (fun c ↦
          (uniqueDirectSumEquiv (K := K) (ι := ι) (U := U) c).toLinearMap ∘ₗ
            Tensor.indexedInclude (K := K) (V := fun _ : ι ↦ U) (default : ι) c) T =
        Tensor.map
          (fun c ↦ (uniqueDirectSumEquiv (K := K) (ι := ι) (U := U) c).toLinearMap)
          (Tensor.map
            (Tensor.indexedInclude (K := K) (V := fun _ : ι ↦ U) (default : ι)) T) := by
    rw [Tensor.map_comp]
    rfl
  rw [← hcomp, hleg]
  simp

end Unique

end Isomorphic

namespace RankLE

/-- A rank bound for an indexed direct sum is unchanged when every constituent and ambient leg
is permuted together. -/
theorem permute_indexedDirectSum {r : ℕ} {T : ∀ i, Tensor3 K (V i)}
    (h : RankLE r (Tensor.indexedDirectSum T)) (e : Orientation) :
    RankLE r
      (Tensor.indexedDirectSum (V := fun i c => V i (e.symm c))
        (fun i => Tensor.permute e (T i))) := by
  have h' := h.permute e
  rwa [Tensor.permute_indexedDirectSum] at h'

/-- Rank upper bounds add over a finite indexed direct sum. -/
theorem indexedDirectSum {r : ι → ℕ} {T : ∀ i, Tensor3 K (V i)}
    (h : ∀ i, RankLE (r i) (T i)) :
    RankLE (∑ i, r i) (Tensor.indexedDirectSum T) := by
  classical
  have aux : ∀ s : Finset ι,
      RankLE (∑ i ∈ s, r i)
        (∑ i ∈ s, Tensor.map (indexedInclude (K := K) (V := V) i) (T i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (RankLE.zero (K := K) (V := IndexedDirectSumSpace K V))
    | @insert i s hi ih =>
        simpa [Finset.sum_insert hi] using
          ((h i).map (indexedInclude (K := K) (V := V) i)).add ih
  simpa [Tensor.indexedDirectSum] using aux (Finset.univ : Finset ι)

end RankLE

namespace BorderRankLE

/-- Constructive border-rank upper bounds add over a finite indexed direct sum. -/
theorem indexedDirectSum {r : ι → ℕ} {T : ∀ i, Tensor3 K (V i)}
    (h : ∀ i, BorderRankLE (r i) (T i)) :
    BorderRankLE (∑ i, r i) (Tensor.indexedDirectSum T) := by
  classical
  have aux : ∀ s : Finset ι,
      BorderRankLE (∑ i ∈ s, r i)
        (∑ i ∈ s, Tensor.map (indexedInclude (K := K) (V := V) i) (T i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (BorderRankLE.zero (K := K) (V := IndexedDirectSumSpace K V))
    | @insert i s hi ih =>
        simpa [Finset.sum_insert hi] using
          ((h i).map (indexedInclude (K := K) (V := V) i)).add ih
  simpa [Tensor.indexedDirectSum] using aux (Finset.univ : Finset ι)

end BorderRankLE

end AlgebraicComplexity.Tensor
