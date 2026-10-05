/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Concise
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Two-legged tensors: the `Z`-contraction and its matrix rank

Several results of the speedup literature — [AlmanLi2026, Propositions 5.3 and 5.4],
[Strassen1988, Lemma 3.12] — quantify over the *rank of a contracted slice*: for a linear
functional `ζ` on the `Z` leg of `S`, the contraction `M = (id ⊗ id ⊗ ζ) S` is a matrix, and the
statements constrain `rank M`.  This file supplies that interface.

## The design choice, and the alternatives that were rejected

A two-legged object could be modelled in at least three ways.

1. **A `Tensor3` whose `Z` leg is the scalar field `K`.**  Then the existing `RankLE`/`Restricts`
   calculus applies verbatim and `⟨1,r,1⟩` is literally a rank-`r` matrix.  Rejected in this
   form: the leg family `fun c ↦ match c with | .X => U | .Y => V | .Z => K` is defined by a
   match on `Leg`, so its `AddCommMonoid`/`Module` instances have to be produced by `cases`,
   which puts a `Leg.rec` between the two instances of every algebraic diamond and forces the
   `X`, `Y` and `Z` legs into one universe.  It also fixes a *new* space in which the contracted
   matrix lives, so every client has to transport along it.
2. **A standalone two-legged rank on `U ⊗[K] V`.**  Rejected: it duplicates the rank calculus
   (`RankLE`, `Restricts`, direct sums) in a second, incompatible shape, and the free-lunch
   theorem that consumes it speaks about `Tensor3`s throughout.
3. **Mathlib's `LinearMap.rank` / `Matrix.rank` used directly.**  Adopted, in the basis-free
   `LinearMap` form: the *only* thing this file adds to `Tensor3` is a flattening
   `matrixFlatten ζ S : (V .Y)ᵛ →ₗ[K] V .X`, and matrix rank is `finrank` of its range.

So there is no new tensor space and no new leg family: a "two-legged tensor" is a `Tensor3`
*together with* a functional `ζ` on its `Z` leg, and the two facts every client needs —
"rank drops by at most the codimension" and "rank `≥ t` gives a restriction onto `⟨1,t,1⟩`" —
are proved about `matrixFlatten`.  The second one lives one layer up, in
`MatrixMultiplication/OneSliceNormalForm.lean`, because it mentions `⟨1,t,1⟩`.

## Main results

* `matrixFlatten`: the `Y`-flattening `(V .Y)ᵛ →ₗ[K] V .X` of a tensor contracted on `Z` by `ζ`.
* `map_ofLegs_eq_sum_pure_of_flatten`: the **structure theorem**.  Whenever the `Y` leg map
  factors through a finite family of functionals `β j` with coefficients `y j`, and the `Z` leg
  map factors through `ζ` with image spanned by `w₀`, the image tensor is the explicit sum
  `∑ j, (a (matrixFlatten ζ S (β j))) ⊗ y j ⊗ w₀`.  Everything else in the two-legged theory is a
  corollary; in particular the flattening is injective on matrices and a matrix is the sum of
  `dim V` pure tensors.
* `matrixFlatten_map_ofLegs`: functoriality, `matrixFlatten ζ' ((a ⊗ b ⊗ c) S) = a ∘ φ ∘ bᵛ`, and
  its corollary `flatten_comp_eq_zero_of_map_eq_zero`.
* `matrixRank_le_add_of_map`: the **rank-drop bound**, `matrixRank S ≤ matrixRank ((a ⊗ b ⊗ c) S)
  + dim (ker a) + dim (ker b)`, the linear-algebra content of [AlmanLi2026, Proposition 5.3].
* `exists_flatten_dual_family`: `t ≤ matrixRank ζ S` produces functionals `β : Fin t → (V .Y)ᵛ`
  and `α : Fin t → (V .X)ᵛ` with `α i (matrixFlatten ζ S (β j)) = if i = j then 1 else 0`, the
  data of the normal form.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Section 5.
* V. Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384 (1988)
  ([Strassen1988]), Lemma 3.12.
-/

namespace AlgebraicComplexity.Tensor

open Module

universe u v w

section Semiring

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- The `Y`-flattening of a tensor contracted on its `Z` leg by `ζ`.

Contracting `S` on `Z` by `ζ` gives a matrix in `V .X ⊗ V .Y`; this is that matrix read as a
linear map from the dual of the `Y` leg to the `X` leg.  In coordinates it is the matrix
`∑_z ζ(e_z) · S[·, ·, z]` acting on row vectors. -/
noncomputable def matrixFlatten (ζ : V .Z →ₗ[K] K) (S : Tensor3 K V) :
    Dual K (V .Y) →ₗ[K] V .X where
  toFun β := contractX β ζ S
  map_add' := by
    intro β₁ β₂
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro a x
      simp only [map_smul, contractX_pure, LinearMap.add_apply, add_mul, add_smul, smul_add]
    · intro T₁ T₂ h₁ h₂
      simp only [map_add, h₁, h₂]
      abel
  map_smul' := by
    intro a β
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro b x
      simp only [map_smul, contractX_pure, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
        smul_smul]
      ring_nf
    · intro T₁ T₂ h₁ h₂
      simp only [map_add, h₁, h₂, RingHom.id_apply, smul_add]

@[simp] theorem matrixFlatten_apply (ζ : V .Z →ₗ[K] K) (S : Tensor3 K V)
    (β : Dual K (V .Y)) : matrixFlatten ζ S β = contractX β ζ S := rfl

@[simp] theorem matrixFlatten_pure (ζ : V .Z →ₗ[K] K) (x : ∀ i, V i) (β : Dual K (V .Y)) :
    matrixFlatten ζ (pure (K := K) x) β = (β (x .Y) * ζ (x .Z)) • x .X := by
  simp [matrixFlatten]

/-- The flattening is linear in the tensor. -/
@[simp] theorem matrixFlatten_add (ζ : V .Z →ₗ[K] K) (S T : Tensor3 K V) :
    matrixFlatten ζ (S + T) = matrixFlatten ζ S + matrixFlatten ζ T := by
  ext β
  simp

@[simp] theorem matrixFlatten_smul (ζ : V .Z →ₗ[K] K) (a : K) (S : Tensor3 K V) :
    matrixFlatten ζ (a • S) = a • matrixFlatten ζ S := by
  ext β
  simp

@[simp] theorem matrixFlatten_zero (ζ : V .Z →ₗ[K] K) :
    matrixFlatten ζ (0 : Tensor3 K V) = 0 := by
  ext β
  simp

/-- The flattening of a finite sum of tensors is the sum of their flattenings. -/
theorem matrixFlatten_finset_sum {ι : Type*} (ζ : V .Z →ₗ[K] K) (s : Finset ι)
    (S : ι → Tensor3 K V) :
    matrixFlatten ζ (∑ i ∈ s, S i) = ∑ i ∈ s, matrixFlatten ζ (S i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, matrixFlatten_add, ih, Finset.sum_insert ha]

/-- **Structure theorem for two-legged tensors.**

Suppose the `Y`-leg map `b` of a legwise restriction factors through the finite family of
functionals `β j` with coefficient vectors `y j`, and the `Z`-leg map `c` factors through `ζ`
with image spanned by `w₀`.  Then the image of `S` is the *explicit* sum of `card ι` pure
tensors whose `X` components are the flattening values `a (matrixFlatten ζ S (β j))`.

Taking `b = id` written in a basis of `V .Y` shows that a matrix is determined by its flattening
and has rank at most `dim (V .Y)`; taking `β` dual to a maximal independent family in the range
of the flattening gives the `⟨1,t,1⟩` normal form. -/
theorem map_ofLegs_eq_sum_pure_of_flatten {ι : Type*} [Fintype ι]
    (S : Tensor3 K V) (ζ : V .Z →ₗ[K] K)
    (β : ι → Dual K (V .Y)) (y : ι → W .Y) (w₀ : W .Z)
    (a : V .X →ₗ[K] W .X) (b : V .Y →ₗ[K] W .Y) (c : V .Z →ₗ[K] W .Z)
    (hb : ∀ v, b v = ∑ j, β j v • y j) (hc : ∀ z, c z = ζ z • w₀) :
    map (ofLegs a b c) S =
      ∑ j, pure (K := K) (ofLegs (a (matrixFlatten ζ S (β j))) (y j) w₀) := by
  classical
  refine PiTensorProduct.induction_on S ?_ ?_
  · intro a₀ x
    have hleft : map (ofLegs a b c) (pure (K := K) x) =
        ∑ j, (β j (x .Y) * ζ (x .Z)) • pure (K := K) (ofLegs (a (x .X)) (y j) w₀) := by
      rw [map_pure, pure_ofLegs_linearMap_apply, hb, hc, pure_ofLegs_smul_Z,
        pure_ofLegs_fintype_sum_Y, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [pure_ofLegs_smul_Y, smul_smul, mul_comm]
    rw [map_smul, hleft, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [matrixFlatten_smul, LinearMap.smul_apply, matrixFlatten_pure, map_smul, map_smul,
      pure_ofLegs_smul_X, pure_ofLegs_smul_X]
  · intro T₁ T₂ h₁ h₂
    rw [map_add, h₁, h₂, matrixFlatten_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [LinearMap.add_apply, map_add, pure_ofLegs_add_X]

/-- Functoriality of the flattening under a legwise restriction whose `Z`-leg map is compatible
with the two contracting functionals. -/
theorem matrixFlatten_map_ofLegs (S : Tensor3 K V)
    (ζ : V .Z →ₗ[K] K) (ζ' : W .Z →ₗ[K] K)
    (a : V .X →ₗ[K] W .X) (b : V .Y →ₗ[K] W .Y) (c : V .Z →ₗ[K] W .Z)
    (hc : ζ' ∘ₗ c = ζ) :
    matrixFlatten ζ' (map (ofLegs a b c) S) = a ∘ₗ matrixFlatten ζ S ∘ₗ b.dualMap := by
  ext β'
  refine PiTensorProduct.induction_on S ?_ ?_
  · intro a₀ x
    have hz : ζ' (c (x .Z)) = ζ (x .Z) := by
      simpa using LinearMap.congr_fun hc (x .Z)
    simp only [map_smul, map_pure, pure_ofLegs_linearMap_apply, matrixFlatten_apply,
      contractX_pure, ofLegs_X, ofLegs_Y, ofLegs_Z, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.dualMap_apply, hz]
  · intro T₁ T₂ h₁ h₂
    simp only [LinearMap.coe_comp, Function.comp_apply, matrixFlatten_apply] at h₁ h₂ ⊢
    simp only [map_add, h₁, h₂]

/-- The tensor-level form of the paper's condition `(A ⊗ B ⊗ ζ) S = 0` implies the flattened
form `A ∘ φ ∘ Bᵛ = 0` used by the one-slice speedup clients.  Only compatibility of the two
contracting functionals, `ζ' ∘ c = ζ`, is required; no finiteness. -/
theorem flatten_comp_eq_zero_of_map_eq_zero (S : Tensor3 K V)
    (ζ : V .Z →ₗ[K] K) (ζ' : W .Z →ₗ[K] K)
    (a : V .X →ₗ[K] W .X) (b : V .Y →ₗ[K] W .Y) (c : V .Z →ₗ[K] W .Z)
    (hc : ζ' ∘ₗ c = ζ) (h : map (ofLegs a b c) S = 0) :
    a ∘ₗ matrixFlatten ζ S ∘ₗ b.dualMap = 0 := by
  rw [← matrixFlatten_map_ofLegs S ζ ζ' a b c hc, h]
  ext β
  simp

end Semiring

section Field

variable {K : Type u} [Field K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- The rank of the matrix obtained by contracting the `Z` leg of `S` with `ζ`. -/
noncomputable def matrixRank (ζ : V .Z →ₗ[K] K) (S : Tensor3 K V) : ℕ :=
  finrank K (LinearMap.range (matrixFlatten ζ S))

/-- A contracted slice has rank at most the dimension of the `X` leg. -/
theorem matrixRank_le_finrank_X [FiniteDimensional K (V .X)]
    (ζ : V .Z →ₗ[K] K) (S : Tensor3 K V) : matrixRank ζ S ≤ finrank K (V .X) :=
  Submodule.finrank_le _

/-- A contracted slice has rank at most the dimension of the `Y` leg. -/
theorem matrixRank_le_finrank_Y [FiniteDimensional K (V .Y)]
    (ζ : V .Z →ₗ[K] K) (S : Tensor3 K V) : matrixRank ζ S ≤ finrank K (V .Y) := by
  have h := LinearMap.finrank_range_le (matrixFlatten ζ S)
  simpa [matrixRank, Subspace.dual_finrank_eq] using h

/-- Mapping a subspace by a linear map loses at most `dim (ker f)` dimensions. -/
private theorem finrank_le_finrank_map_add_ker
    {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [FiniteDimensional K M] (f : M →ₗ[K] N) (p : Submodule K M) :
    finrank K p ≤ finrank K (p.map f) + finrank K (LinearMap.ker f) := by
  have hrn : finrank K (LinearMap.range (f.domRestrict p)) +
      finrank K (LinearMap.ker (f.domRestrict p)) = finrank K p :=
    LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  have hker : finrank K (LinearMap.ker (f.domRestrict p)) ≤ finrank K (LinearMap.ker f) := by
    have hle : Submodule.map p.subtype (LinearMap.ker (f.domRestrict p)) ≤ LinearMap.ker f := by
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.ker_domRestrict] at hx
      simpa using hx
    have hequiv := (Submodule.equivMapOfInjective p.subtype (Submodule.injective_subtype p)
      (LinearMap.ker (f.domRestrict p))).finrank_eq
    exact hequiv.trans_le (Submodule.finrank_mono hle)
  calc finrank K p = finrank K (LinearMap.range (f.domRestrict p)) +
        finrank K (LinearMap.ker (f.domRestrict p)) := hrn.symm
    _ ≤ finrank K (p.map f) + finrank K (LinearMap.ker f) := by
        rw [LinearMap.range_domRestrict]
        exact Nat.add_le_add_left hker _

/-- **Rank drop under a legwise restriction.**

Applying `a` on the `X` leg and `b` on the `Y` leg to a contracted slice lowers its rank by at
most `dim (ker a) + dim (ker b)`.  This is the linear-algebra content of
[AlmanLi2026, Proposition 5.3]: `a` and `b` there are the aggregate maps of the maximal
annihilator subspaces `A'` and `B'`, whose kernels have dimensions at most `dim V'` and
`dim U'`. -/
theorem matrixRank_le_add_of_map [FiniteDimensional K (V .X)] [FiniteDimensional K (V .Y)]
    (S : Tensor3 K V) (ζ : V .Z →ₗ[K] K) (ζ' : W .Z →ₗ[K] K)
    (a : V .X →ₗ[K] W .X) (b : V .Y →ₗ[K] W .Y) (c : V .Z →ₗ[K] W .Z)
    (hc : ζ' ∘ₗ c = ζ) :
    matrixRank ζ S ≤
      matrixRank ζ' (map (ofLegs a b c) S) + finrank K (LinearMap.ker a) +
        finrank K (LinearMap.ker b) := by
  classical
  set φ := matrixFlatten ζ S with hφ
  set P : Submodule K (Dual K (V .Y)) := LinearMap.range b.dualMap with hP
  -- (iii) `dim P + dim (ker b) = dim (V .Y)`.
  have hPb : finrank K P + finrank K (LinearMap.ker b) = finrank K (V .Y) := by
    have h₁ : finrank K P = finrank K (LinearMap.range b) := by
      rw [hP, LinearMap.finrank_range_dualMap_eq_finrank_range]
    rw [h₁]
    exact LinearMap.finrank_range_add_finrank_ker b
  -- (ii) `dim (range φ) + dim (ker φ) = dim (V .Y)`.
  have hφrn : finrank K (LinearMap.range φ) + finrank K (LinearMap.ker φ) = finrank K (V .Y) := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    rwa [Subspace.dual_finrank_eq] at this
  -- (i) mapping `P` by `φ` loses at most `dim (ker φ)`.
  have hi : finrank K P ≤ finrank K (P.map φ) + finrank K (LinearMap.ker φ) :=
    finrank_le_finrank_map_add_ker φ P
  -- (iv) mapping further by `a` loses at most `dim (ker a)`.
  have hiv : finrank K (P.map φ) ≤ finrank K ((P.map φ).map a) + finrank K (LinearMap.ker a) :=
    finrank_le_finrank_map_add_ker a (P.map φ)
  -- (v) identify the range of the flattening of the image.
  have hv : LinearMap.range (matrixFlatten ζ' (map (ofLegs a b c) S)) = (P.map φ).map a := by
    rw [matrixFlatten_map_ofLegs S ζ ζ' a b c hc, ← hφ, LinearMap.range_comp,
      LinearMap.range_comp, ← hP]
  have hrange : matrixRank ζ' (map (ofLegs a b c) S) = finrank K ((P.map φ).map a) := by
    rw [matrixRank, hv]
  -- Combine.
  have key : finrank K (LinearMap.range φ) ≤ finrank K (P.map φ) + finrank K (LinearMap.ker b) := by
    omega
  rw [matrixRank, ← hφ, hrange]
  omega

/-- Extract the normal-form data of a contracted slice of rank at least `t`: functionals `β` on
the `Y` leg whose flattening values are linearly independent, together with a dual family `α` on
the `X` leg.  This is the input of the `⟨1,t,1⟩` identification. -/
theorem exists_flatten_dual_family (ζ : V .Z →ₗ[K] K) (S : Tensor3 K V) (t : ℕ)
    (ht : t ≤ matrixRank ζ S) :
    ∃ (β : Fin t → Dual K (V .Y)) (α : Fin t → Dual K (V .X)),
      ∀ i j, α i (matrixFlatten ζ S (β j)) = if i = j then 1 else 0 := by
  classical
  set φ := matrixFlatten ζ S with hφ
  obtain ⟨w, hw⟩ :
      ∃ w : Fin t → LinearMap.range φ, LinearIndependent K w :=
    exists_linearIndependent_of_le_finrank (R := K) (M := LinearMap.range φ) ht
  -- Lift each `w j` to a functional on the `Y` leg.
  choose β hβ using fun j ↦ (LinearMap.mem_range).1 (w j).2
  set u : Fin t → V .X := fun j ↦ (w j : V .X) with hu
  have huli : LinearIndependent K u := by
    exact hw.map' (LinearMap.range φ).subtype (Submodule.ker_subtype _)
  -- A dual family for the independent family `u`, obtained from the basis of its span.
  set p : Submodule K (V .X) := Submodule.span K (Set.range u) with hp
  set bs : Basis (Fin t) K p := Basis.span huli with hbs
  obtain ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype p)
  refine ⟨β, fun i ↦ bs.coord i ∘ₗ g, fun i j ↦ ?_⟩
  have hmem : u j ∈ p := Submodule.subset_span (Set.mem_range_self j)
  have hgu : g (u j) = ⟨u j, hmem⟩ := by
    have := LinearMap.congr_fun hg (⟨u j, hmem⟩ : p)
    simpa using this
  have hbsj : bs j = (⟨u j, hmem⟩ : p) := by
    rw [hbs, Basis.span_apply]
  have hval : φ (β j) = u j := by rw [hu, hβ j]
  simp only [LinearMap.coe_comp, Function.comp_apply, hval, hgu, ← hbsj,
    Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

end Field

end AlgebraicComplexity.Tensor
