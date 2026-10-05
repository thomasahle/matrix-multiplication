/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.Rank
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Embedding

/-!
# Rank decompositions as reusable multiplication slots

A rank-`r` decomposition is an algorithm with at most `r` scalar multiplication slots.  Padding
with zero slots turns the list-based `RankLE` certificate into an exact `Fin r`-indexed sum.  If
each scalar slot is then replaced by an arbitrary tensor `S`, `r` independent copies of `S`
restrict to the external product `T ⊠ S`.

The final restriction theorem is the tensor-theoretic substitution principle used in
Schönhage's multiple-compression argument.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

private theorem directSum_lof_apply_decidableEq_irrel
    {R ι : Type*} [Semiring R] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (d₁ d₂ : DecidableEq ι) (i : ι) (x : M i) :
    (@DirectSum.lof R _ ι M _ _ d₁ i) x =
      (@DirectSum.lof R _ ι M _ _ d₂ i) x := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  rfl

namespace RankLE

/-- Pad a list rank certificate by zero pure tensors to obtain exactly `r` indexed slots. -/
theorem fin_decomposition {r : ℕ} {T : Tensor3 K V} (h : RankLE r T) :
    ∃ terms : Fin r → (∀ c, V c), T = ∑ i, pure (K := K) (terms i) := by
  classical
  rcases h with ⟨terms, hlength, hsum⟩
  let e : Fin terms.length ↪ Fin r := Fin.castLEEmb hlength
  let padded : Fin r → (∀ c, V c) := Function.extend e terms.get 0
  refine ⟨padded, hsum.trans ?_⟩
  calc
    (terms.map (pure (K := K))).sum =
        ∑ i : Fin terms.length, pure (K := K) (terms.get i) :=
      list_map_sum_eq_fin_sum (pure (K := K)) terms
    _ = ∑ j : Fin r, pure (K := K) (padded j) := by
      apply Fintype.sum_of_injective e e.injective
      · intro j hj
        have hpadded : padded j = 0 := by
          apply Function.extend_apply'
          simpa only [Set.mem_range, not_exists] using hj
        rw [hpadded]
        exact (PiTensorProduct.tprod K).map_coord_zero .X rfl
      · intro i
        exact congrArg (pure (K := K))
          (e.injective.extend_apply terms.get 0 i).symm

/-- An exact finite family of pure terms is a list-based `RankLE` certificate. -/
theorem of_fin_decomposition {r : ℕ} {T : Tensor3 K V}
    (terms : Fin r → (∀ c, V c))
    (h : T = ∑ i, pure (K := K) (terms i)) : RankLE r T := by
  refine ⟨List.ofFn terms, by simp, ?_⟩
  rw [h, ← Fin.sum_ofFn]
  simp [Function.comp_def]

end RankLE

/-- On each leg, replace the `i`th independent copy by tensoring with the `i`th rank-one slot. -/
noncomputable def indexedCopiesExternalMap {r : ℕ}
    (terms : Fin r → (∀ c, V c)) : ∀ c,
    IndexedDirectSumSpace K (fun _ : Fin r ↦ W) c →ₗ[K]
      TensorProduct K (V c) (W c) := by
  classical
  exact fun c ↦ DirectSum.toModule K (Fin r) _ fun i ↦
    (TensorProduct.mk K (V c) (W c)) (terms i c)

theorem indexedCopiesExternalMap_comp_include {r : ℕ}
    (terms : Fin r → (∀ c, V c)) (i : Fin r) (c : Leg) :
    indexedCopiesExternalMap (K := K) terms c ∘ₗ
        indexedInclude (K := K) (V := fun _ : Fin r ↦ W) i c =
      (TensorProduct.mk K (V c) (W c)) (terms i c) := by
  classical
  ext y
  simp only [LinearMap.comp_apply, indexedCopiesExternalMap, indexedInclude]
  convert DirectSum.toModule_lof
    (R := K) (M := fun _ : Fin r ↦ W c)
    (φ := fun i ↦ (TensorProduct.mk K (V c) (W c)) (terms i c)) i y using 1
  apply congrArg (fun z ↦
    (DirectSum.toModule K (Fin r) (TensorProduct K (V c) (W c))
      (fun i ↦ (TensorProduct.mk K (V c) (W c)) (terms i c))) z)
  exact directSum_lof_apply_decidableEq_irrel
    (R := K) (M := fun _ : Fin r ↦ W c) _ _ i y

/-- Tensoring an arbitrary tensor on the left by a pure tensor is the corresponding legwise
`TensorProduct.mk` map. -/
theorem map_tensorProductMk_eq_external_pure
    (x : ∀ c, V c) (S : Tensor3 K W) :
    map (fun c ↦ (TensorProduct.mk K (V c) (W c)) (x c)) S =
      external (pure (K := K) x) S := by
  refine PiTensorProduct.induction_on S ?_ ?_
  · intro a y
    simp
  · intro S₁ S₂ h₁ h₂
    simp only [LinearMap.map_add, h₁, h₂]

/-- Applying the substitution maps to independent copies gives the external product of the sum
of the corresponding pure slots with `S`. -/
theorem map_indexedCopiesExternalMap_indexedDirectSum {r : ℕ}
    (terms : Fin r → (∀ c, V c)) (S : Tensor3 K W) :
    map (indexedCopiesExternalMap (K := K) terms)
        (indexedDirectSum (fun _ : Fin r ↦ S)) =
      external (∑ i, pure (K := K) (terms i)) S := by
  classical
  unfold indexedDirectSum
  rw [map_sum, LinearMap.map_sum₂]
  apply Finset.sum_congr rfl
  intro i _
  calc
    map (indexedCopiesExternalMap (K := K) terms)
        (map (indexedInclude (K := K) (V := fun _ : Fin r ↦ W) i) S) =
      map (fun c ↦ indexedCopiesExternalMap (K := K) terms c ∘ₗ
        indexedInclude (K := K) (V := fun _ : Fin r ↦ W) i c) S := by
          rw [map_comp]
          rfl
    _ = map (fun c ↦ (TensorProduct.mk K (V c) (W c)) (terms i c)) S := by
      congr 2
      funext c
      exact indexedCopiesExternalMap_comp_include (K := K) terms i c
    _ = external (pure (K := K) (terms i)) S :=
      map_tensorProductMk_eq_external_pure (K := K) (terms i) S

/-- Variant of `indexedCopiesExternalMap` whose independent copies are labelled by an arbitrary
finite type equivalent to the rank slots. -/
noncomputable def indexedCopiesExternalMapAlong
    {r : ℕ} {ι : Type x} [Fintype ι] (e : ι ≃ Fin r)
    (terms : Fin r → (∀ c, V c)) : ∀ c,
    IndexedDirectSumSpace K (fun _ : ι ↦ W) c →ₗ[K]
      TensorProduct K (V c) (W c) := by
  classical
  exact fun c ↦ DirectSum.toModule K ι _ fun i ↦
    (TensorProduct.mk K (V c) (W c)) (terms (e i) c)

theorem indexedCopiesExternalMapAlong_comp_include
    {r : ℕ} {ι : Type x} [Fintype ι] (e : ι ≃ Fin r)
    (terms : Fin r → (∀ c, V c)) (i : ι) (c : Leg) :
    indexedCopiesExternalMapAlong (K := K) e terms c ∘ₗ
        indexedInclude (K := K) (V := fun _ : ι ↦ W) i c =
      (TensorProduct.mk K (V c) (W c)) (terms (e i) c) := by
  classical
  ext y
  simp only [LinearMap.comp_apply, indexedCopiesExternalMapAlong, indexedInclude]
  convert DirectSum.toModule_lof
    (R := K) (M := fun _ : ι ↦ W c)
    (φ := fun i ↦ (TensorProduct.mk K (V c) (W c)) (terms (e i) c)) i y using 1

/-- Substitution over an arbitrary finite labelling of the rank slots. -/
theorem map_indexedCopiesExternalMapAlong_indexedDirectSum
    {r : ℕ} {ι : Type x} [Fintype ι] (e : ι ≃ Fin r)
    (terms : Fin r → (∀ c, V c)) (S : Tensor3 K W) :
    map (indexedCopiesExternalMapAlong (K := K) e terms)
        (indexedDirectSum (fun _ : ι ↦ S)) =
      external (∑ i, pure (K := K) (terms i)) S := by
  classical
  unfold indexedDirectSum
  rw [map_sum, LinearMap.map_sum₂]
  calc
    (∑ i : ι,
        map (indexedCopiesExternalMapAlong (K := K) e terms)
          (map (indexedInclude (K := K) (V := fun _ : ι ↦ W) i) S)) =
        ∑ i : ι, external (pure (K := K) (terms (e i))) S := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        map (indexedCopiesExternalMapAlong (K := K) e terms)
            (map (indexedInclude (K := K) (V := fun _ : ι ↦ W) i) S) =
          map (fun c ↦ indexedCopiesExternalMapAlong (K := K) e terms c ∘ₗ
            indexedInclude (K := K) (V := fun _ : ι ↦ W) i c) S := by
              rw [map_comp]
              rfl
        _ = map (fun c ↦
              (TensorProduct.mk K (V c) (W c)) (terms (e i) c)) S := by
          congr 2
          funext c
          exact indexedCopiesExternalMapAlong_comp_include
            (K := K) e terms i c
        _ = external (pure (K := K) (terms (e i))) S :=
          map_tensorProductMk_eq_external_pure (K := K) (terms (e i)) S
    _ = ∑ i : Fin r, external (pure (K := K) (terms i)) S :=
      Equiv.sum_comp e (fun i : Fin r ↦ external (pure (K := K) (terms i)) S)

namespace RankLE

/-- **Tensor substitution.** If `T` has a rank decomposition with at most `r` terms, then `r`
independent copies of any tensor `S` restrict to the external product `T ⊠ S`. -/
theorem indexedCopies_restricts_external {r : ℕ} {T : Tensor3 K V}
    (h : RankLE r T) (S : Tensor3 K W) :
    Restricts (Tensor.indexedDirectSum (fun _ : Fin r ↦ S)) (Tensor.external T S) := by
  rcases h.fin_decomposition with ⟨terms, hterms⟩
  refine ⟨indexedCopiesExternalMap (K := K) terms, ?_⟩
  rw [map_indexedCopiesExternalMap_indexedDirectSum, ← hterms]

/-- Tensor substitution when the independent copies are labelled by an arbitrary finite type
equivalent to the `r` rank slots. -/
theorem indexedCopies_restricts_external_equiv
    {r : ℕ} {ι : Type x} [Fintype ι] {T : Tensor3 K V}
    (h : RankLE r T) (e : ι ≃ Fin r) (S : Tensor3 K W) :
    Restricts (Tensor.indexedDirectSum (fun _ : ι ↦ S)) (Tensor.external T S) := by
  rcases h.fin_decomposition with ⟨terms, hterms⟩
  refine ⟨indexedCopiesExternalMapAlong (K := K) e terms, ?_⟩
  rw [map_indexedCopiesExternalMapAlong_indexedDirectSum, ← hterms]

/-- Cardinality-facing tensor substitution.  A family indexed by `ι` supplies exactly
`Fintype.card ι` multiplication slots. -/
theorem indexedCopies_restricts_external_card
    {ι : Type x} [Fintype ι] {T : Tensor3 K V}
    (h : RankLE (Fintype.card ι) T) (S : Tensor3 K W) :
    Restricts (Tensor.indexedDirectSum (fun _ : ι ↦ S)) (Tensor.external T S) :=
  h.indexedCopies_restricts_external_equiv (Fintype.equivFin ι) S

end RankLE

end AlgebraicComplexity.Tensor
