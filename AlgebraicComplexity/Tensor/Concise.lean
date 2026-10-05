/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Tensor conciseness and flattening lower bounds

A tensor is concise in one leg when contracting all other legs spans that leg.  The formulation is
basis-free: contractions use arbitrary elements of the dual spaces, and the resulting dimension
bounds apply to every constructive rank certificate.  `IsConcise` packages conciseness on all
three legs and yields the standard maximum-dimension lower bound for tensor rank.

The two halves of the basis-free part of the file have different hypotheses.  The contractions and
the conciseness predicates only need a commutative semiring of scalars and additive monoids on the
three legs.  The flattening lower bounds are stated over a field, where finite dimension is
available; they all factor through the single private helper `finrank_le_of_contract_span`, which
turns a decomposition into at most `r` pure tensors into a spanning family of `r` leg vectors.

A third, coordinate-level part closes the file: `IsCoordinateConcise T i` says that the slices of a
*coefficient table* in the direction of leg `i` span that leg.  Only the definition, the
pointwise-product infrastructure it rests on, and the two facts needing nothing else are here; its
interaction with Kronecker products, relabellings and powers lives in
`Tensor/IndependenceNumber.lean`, which owns that coordinate calculus.
-/

namespace AlgebraicComplexity.Tensor

open Function Set Submodule

universe u v w

section Contractions

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]

/-- Contract the `Y` and `Z` legs, retaining the vector on the `X` leg. -/
def contractXMultilinear
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) :
    MultilinearMap K V (V .X) :=
  MultilinearMap.mk'
    (fun x ↦ (fy (x .Y) * fz (x .Z)) • x .X)
    (fun x i a b ↦ by
      cases i <;>
        simp [add_smul, add_mul, mul_add])
    (fun x i a b ↦ by
      cases i <;>
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc])

/-- The linear contraction map induced on the tensor product. -/
def contractX (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) :
    Tensor3 K V →ₗ[K] V .X :=
  PiTensorProduct.lift (contractXMultilinear fy fz)

@[simp] theorem contractX_pure
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (x : ∀ i, V i) :
    contractX fy fz (pure (K := K) x) =
      (fy (x .Y) * fz (x .Z)) • x .X := by
  simp [contractX, contractXMultilinear]

/-- Contract the `X` and `Z` legs, retaining the vector on the `Y` leg. -/
def contractYMultilinear
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) :
    MultilinearMap K V (V .Y) :=
  MultilinearMap.mk'
    (fun x ↦ (fx (x .X) * fz (x .Z)) • x .Y)
    (fun x i a b ↦ by
      cases i <;>
        simp [add_smul, add_mul, mul_add])
    (fun x i a b ↦ by
      cases i <;>
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc])

/-- The `Y`-leg linear contraction induced on the tensor product. -/
def contractY (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) :
    Tensor3 K V →ₗ[K] V .Y :=
  PiTensorProduct.lift (contractYMultilinear fx fz)

@[simp] theorem contractY_pure
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) (x : ∀ i, V i) :
    contractY fx fz (pure (K := K) x) =
      (fx (x .X) * fz (x .Z)) • x .Y := by
  simp [contractY, contractYMultilinear]

/-- Contract the `X` and `Y` legs, retaining the vector on the `Z` leg. -/
def contractZMultilinear
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) :
    MultilinearMap K V (V .Z) :=
  MultilinearMap.mk'
    (fun x ↦ (fx (x .X) * fy (x .Y)) • x .Z)
    (fun x i a b ↦ by
      cases i <;>
        simp [add_smul, add_mul, mul_add])
    (fun x i a b ↦ by
      cases i <;>
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc])

/-- The `Z`-leg linear contraction induced on the tensor product. -/
def contractZ (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) :
    Tensor3 K V →ₗ[K] V .Z :=
  PiTensorProduct.lift (contractZMultilinear fx fy)

@[simp] theorem contractZ_pure
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (x : ∀ i, V i) :
    contractZ fx fy (pure (K := K) x) =
      (fx (x .X) * fy (x .Y)) • x .Z := by
  simp [contractZ, contractZMultilinear]

/-- A tensor is concise in `X` when its `Y,Z` contractions span the full `X` space. -/
def IsConciseX (T : Tensor3 K V) : Prop :=
  Submodule.span K
      (Set.range (fun q : Module.Dual K (V .Y) × Module.Dual K (V .Z) ↦
        contractX q.1 q.2 T)) = ⊤

/-- A tensor is concise in `Y` when its `X,Z` contractions span the full `Y` space. -/
def IsConciseY (T : Tensor3 K V) : Prop :=
  Submodule.span K
      (Set.range (fun q : Module.Dual K (V .X) × Module.Dual K (V .Z) ↦
        contractY q.1 q.2 T)) = ⊤

/-- A tensor is concise in `Z` when its `X,Y` contractions span the full `Z` space. -/
def IsConciseZ (T : Tensor3 K V) : Prop :=
  Submodule.span K
      (Set.range (fun q : Module.Dual K (V .X) × Module.Dual K (V .Y) ↦
        contractZ q.1 q.2 T)) = ⊤

/-- A trilinear tensor is concise when it is concise on each of its three legs. -/
def IsConcise (T : Tensor3 K V) : Prop :=
  IsConciseX T ∧ IsConciseY T ∧ IsConciseZ T

end Contractions

section Flattening

variable {K : Type u} [Field K]
variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- The pure-tensor terms of a list decomposition, reindexed by `Fin terms.length`. -/
private theorem sum_pure_eq_fin_sum (terms : List (∀ i, V i)) :
    (terms.map (pure (K := K))).sum =
      ∑ j : Fin terms.length, pure (K := K) (terms.get j) :=
  list_map_sum_eq_fin_sum (pure (K := K)) terms

/-- Generic single-leg flattening bound, shared by the three conciseness corollaries below.

Given a decomposition of a tensor into the `terms.length` pure tensors of `terms` and a family
`leg` of `terms.length` vectors of `M` such that every contraction `contract q` of every pure term
lies in the span of `leg`, the whole image of the contraction family lies in that span.  If the
contractions of the decomposed tensor already span `M`, then `leg` spans `M`, so `M` has dimension
at most `terms.length ≤ r`.

In the applications `contract` ranges over pairs of dual vectors on the two contracted legs, `M` is
the remaining leg space, and `leg` picks that leg's component out of each term. -/
private theorem finrank_le_of_contract_span
    {M : Type*} [AddCommGroup M] [Module K M]
    {ι : Type*} (contract : ι → Tensor3 K V →ₗ[K] M) {r : ℕ}
    (terms : List (∀ i, V i)) (hlength : terms.length ≤ r)
    (leg : Fin terms.length → M)
    (hterm : ∀ (q : ι) (j : Fin terms.length),
      contract q (pure (K := K) (terms.get j)) ∈ Submodule.span K (Set.range leg))
    (hspan : Submodule.span K
      (Set.range fun q ↦ contract q (terms.map (pure (K := K))).sum) = ⊤) :
    Module.finrank K M ≤ r := by
  have hleg : Submodule.span K (Set.range leg) = ⊤ := by
    apply le_antisymm le_top
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    show contract q (terms.map (pure (K := K))).sum ∈ Submodule.span K (Set.range leg)
    rw [sum_pure_eq_fin_sum, map_sum]
    exact Submodule.sum_mem _ fun j _ ↦ hterm q j
  exact (finrank_le_of_span_eq_top hleg).trans (by simpa using hlength)

/-- Conciseness in `X` makes the dimension of the `X` space a lower bound for tensor rank. -/
theorem RankLE.finrank_X_le {r : ℕ} {T : Tensor3 K V}
    (hT : RankLE r T) (hconcise : IsConciseX T) :
    Module.finrank K (V .X) ≤ r := by
  rcases hT with ⟨terms, hlength, rfl⟩
  refine finrank_le_of_contract_span
      (fun q : Module.Dual K (V .Y) × Module.Dual K (V .Z) ↦ contractX q.1 q.2)
      terms hlength (fun j ↦ (terms.get j) .X) ?_ ?_
  · intro q j
    rw [contractX_pure]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · exact hconcise

/-- Conciseness in `Y` makes the dimension of the `Y` space a lower bound for tensor rank. -/
theorem RankLE.finrank_Y_le {r : ℕ} {T : Tensor3 K V}
    (hT : RankLE r T) (hconcise : IsConciseY T) :
    Module.finrank K (V .Y) ≤ r := by
  rcases hT with ⟨terms, hlength, rfl⟩
  refine finrank_le_of_contract_span
      (fun q : Module.Dual K (V .X) × Module.Dual K (V .Z) ↦ contractY q.1 q.2)
      terms hlength (fun j ↦ (terms.get j) .Y) ?_ ?_
  · intro q j
    rw [contractY_pure]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · exact hconcise

/-- Conciseness in `Z` makes the dimension of the `Z` space a lower bound for tensor rank. -/
theorem RankLE.finrank_Z_le {r : ℕ} {T : Tensor3 K V}
    (hT : RankLE r T) (hconcise : IsConciseZ T) :
    Module.finrank K (V .Z) ≤ r := by
  rcases hT with ⟨terms, hlength, rfl⟩
  refine finrank_le_of_contract_span
      (fun q : Module.Dual K (V .X) × Module.Dual K (V .Y) ↦ contractZ q.1 q.2)
      terms hlength (fun j ↦ (terms.get j) .Z) ?_ ?_
  · intro q j
    rw [contractZ_pure]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · exact hconcise

/-- The rank of a concise tensor is at least the largest of its three leg dimensions. -/
theorem RankLE.max_finrank_le {r : ℕ} {T : Tensor3 K V}
    (hT : RankLE r T) (hconcise : IsConcise T) :
    max (Module.finrank K (V .X))
        (max (Module.finrank K (V .Y)) (Module.finrank K (V .Z))) ≤ r := by
  rw [max_le_iff, max_le_iff]
  exact ⟨hT.finrank_X_le hconcise.1,
    hT.finrank_Y_le hconcise.2.1, hT.finrank_Z_le hconcise.2.2⟩

end Flattening

/-! ## Conciseness in coordinates

The predicates above are basis-free.  Clients that present a tensor by an explicit coefficient
table need the same notion read off the table, and they need it *for every Kronecker power*, where
the passage to powers becomes a statement about spans of pointwise products of functions.

`IsCoordinateConcise T i` says that the slices of the coefficient table `T` in the direction of
leg `i` span the coordinate space of that leg.  Its stability under Kronecker products, its
consequences for rank and asymptotic rank, and everything else that mentions the coordinate
calculus of `Tensor/IndependenceNumber.lean` live there; this file carries the definition, the
pointwise-product infrastructure it rests on, and the two facts that need nothing else.

The comparison `IsCoordinateConcise T i ↔ IsConcise_i (coordinateTensor T)` is not proved.
-/

section MulPair

variable (K : Type u) [Field K] (α : Type v) (β : Type w)

/-- The pointwise product of a function on `α` and a function on `β`, as a bilinear map into the
functions on `α × β`. -/
def mulPair : (α → K) →ₗ[K] (β → K) →ₗ[K] ((α × β) → K) where
  toFun u :=
    { toFun := fun v q ↦ u q.1 * v q.2
      map_add' := fun v v' ↦ by funext q; simp [mul_add]
      map_smul' := fun a v ↦ by funext q; simp [mul_left_comm] }
  map_add' u u' := by
    ext v q
    simp [add_mul]
  map_smul' a u := by
    ext v q
    simp [mul_assoc]

@[simp] theorem mulPair_apply (u : α → K) (v : β → K) (q : α × β) :
    mulPair K α β u v q = u q.1 * v q.2 := rfl

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [Fintype α] [Fintype β] in
/-- The standard basis vector of a pair is the pointwise product of the two standard basis
vectors. -/
theorem mulPair_single (x : α) (y : β) :
    mulPair K α β (Pi.single x 1) (Pi.single y 1) = Pi.single (x, y) 1 := by
  funext q
  rw [mulPair_apply, Pi.single_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : q = (x, y)
  · rw [if_pos h, if_pos (show q.1 = x by rw [h]), if_pos (show q.2 = y by rw [h]), one_mul]
  · rw [if_neg h]
    by_cases h1 : q.1 = x
    · rw [if_pos h1, if_neg, mul_zero]
      intro h2
      exact h (Prod.ext h1 h2)
    · rw [if_neg h1, zero_mul]

/-- **Pointwise products of two spanning families span.** -/
theorem span_image2_mulPair {S : Set (α → K)} {T : Set (β → K)}
    (hS : span K S = ⊤) (hT : span K T = ⊤) :
    span K (Set.image2 (fun u v ↦ mulPair K α β u v) S T) = ⊤ := by
  rw [← Submodule.map₂_span_span, hS, hT]
  refine le_antisymm le_top ?_
  have hbasis : span K (Set.range fun q : α × β ↦ (Pi.single q 1 : (α × β) → K)) = ⊤ := by
    have hfun : (fun q : α × β ↦ (Pi.single q 1 : (α × β) → K)) =
        ⇑(Pi.basisFun K (α × β)) := by
      funext q
      simp
    rw [hfun]
    exact (Pi.basisFun K (α × β)).span_eq
  rw [← hbasis]
  refine span_le.mpr ?_
  rintro _ ⟨q, rfl⟩
  show (Pi.single q 1 : (α × β) → K) ∈ map₂ (mulPair K α β) ⊤ ⊤
  have hq : (Pi.single q 1 : (α × β) → K) =
      mulPair K α β (Pi.single q.1 1) (Pi.single q.2 1) := by
    rw [mulPair_single]
  rw [hq]
  exact Submodule.apply_mem_map₂ _ Submodule.mem_top Submodule.mem_top

end MulPair

section CoordinateConcise

variable {K : Type u} [Field K] {κ : Leg → Type v}

/-- The **slice** of a coefficient table in the direction of leg `i` through the triple `p`. -/
def coordinateSlice (T : (∀ j, κ j) → K) (i : Leg) (p : ∀ j, κ j) : κ i → K :=
  fun x ↦ T (Function.update p i x)

omit [Field K] in
/-- A slice evaluates the table at the triple with the `i`-th coordinate overwritten. -/
theorem coordinateSlice_apply (T : (∀ j, κ j) → K) (i : Leg) (p : ∀ j, κ j) (x : κ i) :
    coordinateSlice T i p x = T (Function.update p i x) := rfl

/-- `T` is **concise on leg `i` in coordinates** when its slices in the direction of leg `i` span
the whole coordinate space of that leg. -/
def IsCoordinateConcise (T : (∀ j, κ j) → K) (i : Leg) : Prop :=
  Submodule.span K (Set.range (coordinateSlice T i)) = ⊤

/-- **Every standard basis vector a slice gives conciseness.**  A coefficient table each of whose
leg-`i` variables `a` admits a triple isolating it --- so that the corresponding slice is exactly
the standard basis vector `e_a` --- is concise on leg `i` in coordinates. -/
theorem isCoordinateConcise_of_forall_single {T : (∀ j, κ j) → K} {i : Leg}
    [Fintype (κ i)] [DecidableEq (κ i)]
    (h : ∀ a : κ i, (Pi.single a (1 : K) : κ i → K) ∈ Set.range (coordinateSlice T i)) :
    IsCoordinateConcise T i := by
  refine le_antisymm le_top ?_
  have hbasis : span K (Set.range fun a : κ i ↦ (Pi.single a (1 : K) : κ i → K)) = ⊤ := by
    have hfun : (fun a : κ i ↦ (Pi.single a (1 : K) : κ i → K)) = ⇑(Pi.basisFun K (κ i)) := by
      funext a
      simp
    rw [hfun]
    exact (Pi.basisFun K (κ i)).span_eq
  rw [← hbasis]
  exact span_le.mpr (by rintro _ ⟨a, rfl⟩; exact Submodule.subset_span (h a))

/-- A table concise on a leg with at least one variable has a nonzero coefficient: otherwise all
its slices vanish and the span of the slices is the zero submodule. -/
theorem exists_ne_zero_of_isCoordinateConcise {T : (∀ j, κ j) → K} {i : Leg} [Nonempty (κ i)]
    (h : IsCoordinateConcise T i) : ∃ p, T p ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hbot : (⊤ : Submodule K (κ i → K)) = ⊥ := by
    rw [← h, Submodule.span_eq_bot]
    rintro _ ⟨p, rfl⟩
    funext x
    exact hcon _
  exact absurd hbot top_ne_bot

end CoordinateConcise

end AlgebraicComplexity.Tensor
