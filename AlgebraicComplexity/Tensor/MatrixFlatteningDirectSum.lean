/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.DirectSum
import AlgebraicComplexity.Tensor.MatrixFlattening

/-!
# Additivity of the contracted slice over a binary direct sum

`Tensor/MatrixFlattening.lean` reads a tensor `S` contracted on its `Z` leg by a functional `ζ`
as a linear map `matrixFlatten ζ S : (V .Y)ᵛ →ₗ[K] V .X` and defines its `matrixRank`.  This file
proves the one structural law that the append constructions of the speedup literature need:
**the contracted slice of a direct sum is the block-diagonal matrix of the two contracted
slices**, and its rank is therefore the sum of the two ranks.

The `Z`-leg functional on the sum is arbitrary; the two summand functionals are its restrictions
`ζ ∘ inl` and `ζ ∘ inr`.  This is what makes the law usable for the paper's `f' = (f, −1)`, whose
two restrictions are `f` and `−1` ([AlmanLi2026, Proposition 5.4, p. 17]).

## Main results

* `matrixFlatten_directSum`: `matrixFlatten ζ (S ⊕ T) = (φ ⊕ ψ) ∘ (β ↦ (β ∘ inl, β ∘ inr))`,
  where `φ` and `ψ` are the two summand flattenings.  The right-hand factor is the splitting of
  a functional on `V .Y × W .Y`; it is surjective, which is the whole content of the rank law.
* `matrixRank_directSum`: `matrixRank ζ (S ⊕ T) = matrixRank (ζ ∘ inl) S + matrixRank (ζ ∘ inr) T`.
* `finrank_submodule_prod`: `dim (p × q) = dim p + dim q` for submodules of a product, the
  linear-algebra lemma the rank law rests on.  It is stated for arbitrary submodules and is
  Mathlib-upstream material.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Proposition 5.4, p. 17.
-/

namespace AlgebraicComplexity.Tensor

open Module

universe u v w

section Semiring

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- **The contracted slice of a direct sum is block diagonal.**

Contracting `S ⊕ T` on its `Z` leg by `ζ` and reading the result as a matrix gives the block
matrix `diag (φ, ψ)`, where `φ` and `ψ` are the slices of `S` and `T` contracted by the two
restrictions `ζ ∘ inl` and `ζ ∘ inr`.  The prefactor splits a functional on the `Y` leg of the
sum into its two restrictions. -/
theorem matrixFlatten_directSum (ζ : (V .Z × W .Z) →ₗ[K] K)
    (S : Tensor3 K V) (T : Tensor3 K W) :
    matrixFlatten ζ (directSum S T) =
      LinearMap.prodMap
          (matrixFlatten (ζ ∘ₗ LinearMap.inl K (V .Z) (W .Z)) S)
          (matrixFlatten (ζ ∘ₗ LinearMap.inr K (V .Z) (W .Z)) T) ∘ₗ
        ((LinearMap.inl K (V .Y) (W .Y)).dualMap.prod
          (LinearMap.inr K (V .Y) (W .Y)).dualMap) := by
  have hL : (includeLeft (K := K) (V := V) (W := W)) =
      ofLegs (V := fun i ↦ V i →ₗ[K] V i × W i)
        (LinearMap.inl K (V .X) (W .X)) (LinearMap.inl K (V .Y) (W .Y))
        (LinearMap.inl K (V .Z) (W .Z)) := by
    funext i; cases i <;> rfl
  have hR : (includeRight (K := K) (V := V) (W := W)) =
      ofLegs (V := fun i ↦ W i →ₗ[K] V i × W i)
        (LinearMap.inr K (V .X) (W .X)) (LinearMap.inr K (V .Y) (W .Y))
        (LinearMap.inr K (V .Z) (W .Z)) := by
    funext i; cases i <;> rfl
  have h1 := matrixFlatten_map_ofLegs (K := K) (V := V) (W := fun i ↦ V i × W i) S
    (ζ ∘ₗ LinearMap.inl K (V .Z) (W .Z)) ζ
    (LinearMap.inl K (V .X) (W .X)) (LinearMap.inl K (V .Y) (W .Y))
    (LinearMap.inl K (V .Z) (W .Z)) rfl
  have h2 := matrixFlatten_map_ofLegs (K := K) (V := W) (W := fun i ↦ V i × W i) T
    (ζ ∘ₗ LinearMap.inr K (V .Z) (W .Z)) ζ
    (LinearMap.inr K (V .X) (W .X)) (LinearMap.inr K (V .Y) (W .Y))
    (LinearMap.inr K (V .Z) (W .Z)) rfl
  simp only [directSum, matrixFlatten_add, hL, hR, h1, h2]
  ext β <;> simp

end Semiring

section Field

variable {K : Type u} [Field K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- The dimension of a product of two submodules is the sum of their dimensions. -/
theorem finrank_submodule_prod {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [FiniteDimensional K M] [FiniteDimensional K N]
    (p : Submodule K M) (q : Submodule K N) :
    finrank K (p.prod q) = finrank K p + finrank K q := by
  have e : (p.prod q) ≃ₗ[K] (p × q) :=
    { toFun := fun x ↦ (⟨x.1.1, (Submodule.mem_prod.1 x.2).1⟩,
        ⟨x.1.2, (Submodule.mem_prod.1 x.2).2⟩)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun z ↦ ⟨(z.1.1, z.2.1), Submodule.mem_prod.2 ⟨z.1.2, z.2.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [e.finrank_eq, Module.finrank_prod]

/-- **Additivity of the contracted-slice rank over a direct sum.**

The rank of the matrix obtained by contracting `S ⊕ T` with `ζ` is the sum of the ranks of the
two contracted summands.  This is the additivity used by [AlmanLi2026, Proposition 5.4, p. 17]
to compute `rank ((id ⊗ id ⊗ f') (S ⊕ ⟨1,s,1⟩)) = q + s`. -/
theorem matrixRank_directSum [FiniteDimensional K (V .X)] [FiniteDimensional K (W .X)]
    (ζ : (V .Z × W .Z) →ₗ[K] K) (S : Tensor3 K V) (T : Tensor3 K W) :
    matrixRank ζ (directSum S T) =
      matrixRank (ζ ∘ₗ LinearMap.inl K (V .Z) (W .Z)) S +
        matrixRank (ζ ∘ₗ LinearMap.inr K (V .Z) (W .Z)) T := by
  have hsurj : LinearMap.range ((LinearMap.inl K (V .Y) (W .Y)).dualMap.prod
      (LinearMap.inr K (V .Y) (W .Y)).dualMap) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨β₁, β₂⟩
    refine ⟨β₁.coprod β₂, ?_⟩
    ext v <;> simp
  rw [matrixRank, matrixFlatten_directSum, LinearMap.range_comp, hsurj, Submodule.map_top,
    LinearMap.range_prodMap, finrank_submodule_prod, matrixRank, matrixRank]

end Field

end AlgebraicComplexity.Tensor
