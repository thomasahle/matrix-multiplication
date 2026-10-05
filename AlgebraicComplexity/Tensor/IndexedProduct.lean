/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# External products of finite indexed direct sums

Mathlib proves that a tensor product of two module direct sums is linearly equivalent to the
direct sum indexed by all pairs.  This file lifts that equivalence to three-legged tensors and
proves that it distributes the external product of two indexed tensor sums into every pair of
constituents.

This is deliberately different from the diagonal projection in `IndexedDirectSum`: no cross
term is discarded here.  It is the algebraic expansion needed for tensor-power type arguments.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w x y z t

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι]
variable {κ : Type x} [Fintype κ]
variable {V : ι → Leg → Type v}
variable [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)]
variable {W : κ → Leg → Type y}
variable [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]

private theorem directSum_lof_apply_decidableEq_irrel
    {R α : Type*} [Semiring R] {M : α → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (d₁ d₂ : DecidableEq α) (i : α) (x : M i) :
    (@DirectSum.lof R _ α M _ _ d₁ i) x =
      (@DirectSum.lof R _ α M _ _ d₂ i) x := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  rfl

/-- The pairwise external-product family indexed by `ι × κ`. -/
abbrev IndexedExternalProductFamily (q : ι × κ) (c : Leg) :=
  TensorProduct K (V q.1 c) (W q.2 c)

/-- The family obtained by externally multiplying every member of `W` by one common left
factor. -/
abbrev IndexedExternalRightFamily
    {U : Leg → Type z}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (j : κ) (c : Leg) :=
  TensorProduct K (U c) (W j c)

/-- On each leg, distribute a common left tensor factor over an indexed direct sum on the right. -/
noncomputable def indexedExternalRightEquiv
    {U : Leg → Type z}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)] : ∀ c,
    TensorProduct K (U c) (IndexedDirectSumSpace K W c) ≃ₗ[K]
      IndexedDirectSumSpace K
        (IndexedExternalRightFamily (K := K) (U := U) (W := W)) c := by
  classical
  exact fun c ↦ TensorProduct.directSumRight K K (U c) (fun j ↦ W j c)

omit [Fintype κ] in
/-- One-sided distributivity carries a tensor with an included right block to the same included
block of the distributed family. -/
theorem indexedExternalRightEquiv_comp_include
    {U : Leg → Type z}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (j : κ) (c : Leg) :
    (indexedExternalRightEquiv (K := K) (U := U) (W := W) c).toLinearMap ∘ₗ
        TensorProduct.map (LinearMap.id (R := K) (M := U c))
          (indexedInclude (K := K) (V := W) j c) =
      indexedInclude (K := K)
        (V := IndexedExternalRightFamily (K := K) (U := U) (W := W)) j c := by
  classical
  apply TensorProduct.ext'
  intro x y
  simp [indexedExternalRightEquiv, indexedInclude,
    IndexedExternalRightFamily]

omit [Fintype κ] in
/-- Tensor-level action of one-sided distributivity on one included summand. -/
theorem map_indexedExternalRightEquiv_external_include
    {U : Leg → Type z}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (j : κ) (T : Tensor3 K U) (S : Tensor3 K (W j)) :
    map (fun c ↦
        (indexedExternalRightEquiv (K := K) (U := U) (W := W) c).toLinearMap)
      (external T (map (indexedInclude (K := K) (V := W) j) S)) =
    map (indexedInclude (K := K)
        (V := IndexedExternalRightFamily (K := K) (U := U) (W := W)) j)
      (external T S) := by
  have hmap :
      map (fun c ↦ TensorProduct.map
          (LinearMap.id (R := K) (M := U c))
          (indexedInclude (K := K) (V := W) j c)) (external T S) =
        external T (map (indexedInclude (K := K) (V := W) j) S) := by
    calc
      _ = external
          (map (fun c ↦ LinearMap.id (R := K) (M := U c)) T)
          (map (indexedInclude (K := K) (V := W) j) S) :=
        map_external
          (fun c ↦ LinearMap.id (R := K) (M := U c))
          (indexedInclude (K := K) (V := W) j) T S
      _ = _ := by simp only [map_id, LinearMap.id_apply]
  rw [← hmap]
  calc
    map (fun c ↦
        (indexedExternalRightEquiv (K := K) (U := U) (W := W) c).toLinearMap)
        (map (fun c ↦ TensorProduct.map
          (LinearMap.id (R := K) (M := U c))
          (indexedInclude (K := K) (V := W) j c)) (external T S)) =
      map (fun c ↦
        (indexedExternalRightEquiv (K := K) (U := U) (W := W) c).toLinearMap ∘ₗ
          TensorProduct.map (LinearMap.id (R := K) (M := U c))
            (indexedInclude (K := K) (V := W) j c)) (external T S) := by
        rw [map_comp]
        rfl
    _ = map (indexedInclude (K := K)
          (V := IndexedExternalRightFamily (K := K) (U := U) (W := W)) j)
        (external T S) := by
      congr 2
      funext c
      exact indexedExternalRightEquiv_comp_include
        (K := K) (U := U) (W := W) j c

/-- A common left tensor distributes isomorphically over a finite indexed direct sum on the
right. -/
theorem map_indexedExternalRightEquiv_external_indexedDirectSum
    {U : Leg → Type z}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (T : Tensor3 K U) (S : ∀ j, Tensor3 K (W j)) :
    map (fun c ↦
        (indexedExternalRightEquiv (K := K) (U := U) (W := W) c).toLinearMap)
      (external T (indexedDirectSum S)) =
    indexedDirectSum (fun j ↦ external T (S j)) := by
  classical
  unfold indexedDirectSum
  rw [external_fintypeSum_right, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact map_indexedExternalRightEquiv_external_include
    (K := K) (U := U) (W := W) j T (S j)

/-- On each leg, distribute a tensor product of indexed direct sums over every pair of summands. -/
noncomputable def indexedExternalEquiv : ∀ c,
    TensorProduct K (IndexedDirectSumSpace K V c) (IndexedDirectSumSpace K W c) ≃ₗ[K]
      IndexedDirectSumSpace K
        (IndexedExternalProductFamily (K := K) (V := V) (W := W)) c := by
  classical
  exact fun c ↦ TensorProduct.directSum K K (fun i ↦ V i c) (fun j ↦ W j c)

omit [Fintype ι] [Fintype κ] in
/-- The distribution equivalence sends a tensor product of two included vectors to the included
vector in the corresponding pair block. -/
theorem indexedExternalEquiv_comp_includes (i : ι) (j : κ) (c : Leg) :
    (indexedExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap ∘ₗ
        TensorProduct.map
          (indexedInclude (K := K) (V := V) i c)
          (indexedInclude (K := K) (V := W) j c) =
      indexedInclude (K := K)
        (V := IndexedExternalProductFamily (K := K) (V := V) (W := W)) (i, j) c := by
  classical
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, indexedExternalEquiv,
    indexedInclude, IndexedExternalProductFamily]
  convert TensorProduct.directSum_lof_tmul_lof K K
    (M₁ := fun i ↦ V i c) (M₂ := fun j ↦ W j c) i x j y using 1
  · apply congrArg (fun z ↦
      (TensorProduct.directSum K K (fun i ↦ V i c) (fun j ↦ W j c)) z)
    congr 1
  · exact directSum_lof_apply_decidableEq_irrel
      (M := fun q : ι × κ ↦ TensorProduct K (V q.1 c) (W q.2 c))
      _ _ (i, j) (x ⊗ₜ[K] y)

omit [Fintype ι] [Fintype κ] in
/-- At tensor level, an external product of two included blocks is carried to the corresponding
included pairwise external product. -/
theorem map_indexedExternalEquiv_external_includes (i : ι) (j : κ)
    (T : Tensor3 K (V i)) (S : Tensor3 K (W j)) :
    map (fun c ↦ (indexedExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap)
        (external
          (map (indexedInclude (K := K) (V := V) i) T)
          (map (indexedInclude (K := K) (V := W) j) S)) =
      map (indexedInclude (K := K)
        (V := IndexedExternalProductFamily (K := K) (V := V) (W := W)) (i, j))
        (external T S) := by
  rw [← map_external]
  calc
    map (fun c ↦ (indexedExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap)
        (map (fun c ↦ TensorProduct.map
          (indexedInclude (K := K) (V := V) i c)
          (indexedInclude (K := K) (V := W) j c)) (external T S)) =
      map (fun c ↦
        (indexedExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap ∘ₗ
          TensorProduct.map
            (indexedInclude (K := K) (V := V) i c)
            (indexedInclude (K := K) (V := W) j c)) (external T S) := by
        rw [map_comp]
        rfl
    _ = map (indexedInclude (K := K)
          (V := IndexedExternalProductFamily (K := K) (V := V) (W := W)) (i, j))
        (external T S) := by
      congr 2
      funext c
      exact indexedExternalEquiv_comp_includes (K := K) (V := V) (W := W) i j c

/-- The full external product of two indexed direct sums is isomorphic to the indexed direct sum
of all pairwise external products. -/
theorem map_indexedExternalEquiv_external_indexedDirectSum
    (T : ∀ i, Tensor3 K (V i)) (S : ∀ j, Tensor3 K (W j)) :
    map (fun c ↦ (indexedExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap)
        (external (indexedDirectSum T) (indexedDirectSum S)) =
      indexedDirectSum (fun q : ι × κ ↦ external (T q.1) (S q.2)) := by
  classical
  unfold indexedDirectSum
  rw [external_sum_sum, map_sum]
  simp_rw [map_sum, map_indexedExternalEquiv_external_includes]
  exact (Fintype.sum_prod_type (fun q : ι × κ ↦
    map (indexedInclude (K := K)
      (V := IndexedExternalProductFamily (K := K) (V := V) (W := W)) q)
      (external (T q.1) (S q.2)))).symm

namespace Isomorphic

/-- Relation-level form of distributing one common left tensor across an indexed direct sum. -/
theorem external_indexedDirectSum_right
    {U : Leg → Type z}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (T : Tensor3 K U) (S : ∀ j, Tensor3 K (W j)) :
    Isomorphic (Tensor.external T (Tensor.indexedDirectSum S))
      (Tensor.indexedDirectSum (fun j ↦ Tensor.external T (S j))) := by
  refine ⟨indexedExternalRightEquiv (K := K) (U := U) (W := W), ?_⟩
  exact map_indexedExternalRightEquiv_external_indexedDirectSum
    (K := K) (U := U) (W := W) T S

/-- Relation-level form of full pairwise distribution over indexed direct sums. -/
theorem external_indexedDirectSum
    (T : ∀ i, Tensor3 K (V i)) (S : ∀ j, Tensor3 K (W j)) :
    Isomorphic (Tensor.external (Tensor.indexedDirectSum T) (Tensor.indexedDirectSum S))
      (Tensor.indexedDirectSum (fun q : ι × κ ↦ Tensor.external (T q.1) (S q.2))) := by
  refine ⟨indexedExternalEquiv (K := K) (V := V) (W := W), ?_⟩
  exact map_indexedExternalEquiv_external_indexedDirectSum T S

/-- The external product of three indexed direct sums is isomorphic to the direct sum of all
triples of constituent products.  The pair indexing follows the left association of `external`. -/
theorem external3_indexedDirectSum
    {η : Type z} [Fintype η]
    {U : η → Leg → Type t}
    [∀ k c, AddCommMonoid (U k c)] [∀ k c, Module K (U k c)]
    (T : ∀ i, Tensor3 K (V i)) (S : ∀ j, Tensor3 K (W j))
    (R : ∀ k, Tensor3 K (U k)) :
    Isomorphic
      (Tensor.external
        (Tensor.external (Tensor.indexedDirectSum T) (Tensor.indexedDirectSum S))
        (Tensor.indexedDirectSum R))
      (Tensor.indexedDirectSum
        (fun q : (ι × κ) × η ↦
          Tensor.external (Tensor.external (T q.1.1) (S q.1.2)) (R q.2))) := by
  exact
    (Isomorphic.external (external_indexedDirectSum T S)
      (Isomorphic.refl (Tensor.indexedDirectSum R))).trans
      (external_indexedDirectSum
        (fun q : ι × κ ↦ Tensor.external (T q.1) (S q.2)) R)

end Isomorphic

end AlgebraicComplexity.Tensor
