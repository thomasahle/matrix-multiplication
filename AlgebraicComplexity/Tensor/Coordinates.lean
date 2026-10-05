/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Basic
import AlgebraicComplexity.Tensor.CoordinatesDefs
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Coordinates for three-legged tensors

This file re-exports the standard coordinate-space abbreviation from
`Tensor/CoordinatesDefs.lean`.  A choice of basis on every leg then identifies an abstract tensor
with its finite coefficient function.  This is the narrow bridge between the basis-free theorem
layer and generated coordinate data.

Beyond the equivalence itself (`coordinateEquiv`, and `standardCoordinateEquiv` for the standard
coordinate spaces `κ i → K`) the file carries the two pieces of bookkeeping every concrete example
needs:

* **Coefficients of standard-basis sums.**  `standardCoordinateEquiv_pure_single` and
  `standardCoordinateEquiv_sum_single` compute the coefficient function of a sum
  `∑ a, coef a • e_{idx a .X} ⊗ e_{idx a .Y} ⊗ e_{idx a .Z}` once, so that the concrete tensors of
  `Tensor/GroupTensor.lean` and `Examples/` do not each redo the case split over the three legs.
* **Legwise relabelling.**  `relabelLegEquiv` is the legwise isomorphism induced by an equivalence
  of index types on every leg; `congr_relabelLegEquiv_pure` says it permutes standard-basis pure
  tensors, and `standardCoordinateEquiv_congr_relabel` transports a whole coefficient function
  along it.
-/

namespace AlgebraicComplexity.Tensor

open Module

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable {κ : Leg → Type w} [∀ i, Finite (κ i)]

/-- The tensor-product basis induced by one basis on each leg. -/
noncomputable def coordinateBasis (b : ∀ i, Module.Basis (κ i) K (V i)) :
    Module.Basis (∀ i, κ i) K (Tensor3 K V) :=
  Basis.piTensorProduct b

/-- Coordinates of an abstract tensor as a finite, finitely supported function. -/
noncomputable def finsuppCoordinateEquiv (b : ∀ i, Module.Basis (κ i) K (V i)) :
    Tensor3 K V ≃ₗ[K] ((∀ i, κ i) →₀ K) :=
  (coordinateBasis b).repr

/-- Coordinates as an ordinary function; the index type is finite. -/
noncomputable def coordinateEquiv (b : ∀ i, Module.Basis (κ i) K (V i)) :
    Tensor3 K V ≃ₗ[K] ((∀ i, κ i) → K) :=
  (finsuppCoordinateEquiv b).trans
    (Finsupp.linearEquivFunOnFinite K K (∀ i, κ i))

@[simp] theorem coordinateEquiv_pure (b : ∀ i, Module.Basis (κ i) K (V i))
    (x : ∀ i, V i) (p : ∀ i, κ i) :
    coordinateEquiv b (pure (K := K) x) p = ∏ i, (b i).repr (x i) (p i) := by
  simp [coordinateEquiv, finsuppCoordinateEquiv, coordinateBasis]

/-- The canonical coefficient equivalence for standard coordinate vector spaces. -/
noncomputable def standardCoordinateEquiv :
    Tensor3 K (CoordinateSpace K κ) ≃ₗ[K] ((∀ i, κ i) → K) :=
  coordinateEquiv (fun i ↦ Pi.basisFun K (κ i))

@[simp] theorem standardCoordinateEquiv_pure
    (x : ∀ i, CoordinateSpace K κ i) (p : ∀ i, κ i) :
    standardCoordinateEquiv (K := K) (κ := κ) (pure (K := K) x) p =
      ∏ i, x i (p i) := by
  simp [standardCoordinateEquiv]

/-- Extensionality for tensors in standard finite coordinates. -/
theorem standardCoordinate_ext {T S : Tensor3 K (CoordinateSpace K κ)}
    (h : ∀ p, standardCoordinateEquiv (K := K) (κ := κ) T p =
      standardCoordinateEquiv (K := K) (κ := κ) S p) : T = S := by
  apply (standardCoordinateEquiv (K := K) (κ := κ)).injective
  funext p
  exact h p

/-- Coordinate formula for restricting functions along maps of finite index types. -/
theorem standardCoordinateEquiv_map_funLeft
    {κ' : Leg → Type*} [∀ i, Finite (κ' i)]
    (e : ∀ i, κ' i → κ i) (T : Tensor3 K (CoordinateSpace K κ))
    (p : ∀ i, κ' i) :
    standardCoordinateEquiv (K := K) (κ := κ')
        (map (fun i ↦ LinearMap.funLeft K K (e i)) T) p =
      standardCoordinateEquiv (K := K) (κ := κ) T (fun i ↦ e i (p i)) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp [standardCoordinateEquiv_pure]
  · intro T₁ T₂ h₁ h₂
    simp [h₁, h₂]

/-! ## Coefficients of standard-basis pure tensors

Almost every concrete tensor in this repository is presented as a finite sum
`∑ a, coef a • e_{idx a .X} ⊗ e_{idx a .Y} ⊗ e_{idx a .Z}` of scaled standard-basis pure tensors.
The two lemmas below compute the coefficient function of such a sum once and for all, so that
individual examples do not each repeat the eight-way case split over the three legs. -/

section StandardBasis

variable [∀ i, DecidableEq (κ i)]

/-- The coefficient function of a pure tensor of standard basis vectors is the indicator of its
index: `e_{p .X} ⊗ e_{p .Y} ⊗ e_{p .Z}` has coefficient `1` at `p` and `0` elsewhere. -/
@[simp] theorem standardCoordinateEquiv_pure_single (p q : ∀ i, κ i) :
    standardCoordinateEquiv (K := K) (κ := κ)
        (pure (K := K) (fun i ↦ (Pi.single (p i) (1 : K) : κ i → K))) q =
      if p = q then 1 else 0 := by
  rw [standardCoordinateEquiv_pure, prod_leg]
  simp only [Pi.single_apply]
  by_cases hx : q .X = p .X <;> by_cases hy : q .Y = p .Y <;> by_cases hz : q .Z = p .Z <;>
    simp only [hx, hy, hz, if_true, if_false, mul_one, mul_zero]
  · rw [if_pos]; funext i; cases i <;> simp [hx, hy, hz]
  all_goals rw [if_neg]; intro hpq; subst hpq; simp_all

/-- The coefficient function of a finite sum of scaled standard-basis pure tensors collects the
coefficients of the summands sitting at the requested index.

This is the single computation behind every concrete support formula in `Tensor/GroupTensor.lean`
and `Examples/`: instantiate `idx` with the address of each summand and evaluate the filter. -/
theorem standardCoordinateEquiv_sum_single {α : Type*} [Fintype α] [DecidableEq (∀ i, κ i)]
    (coef : α → K) (idx : α → ∀ i, κ i) (q : ∀ i, κ i) :
    standardCoordinateEquiv (K := K) (κ := κ)
        (∑ a, coef a • pure (K := K) (fun i ↦ (Pi.single (idx a i) (1 : K) : κ i → K))) q =
      ∑ a ∈ Finset.univ.filter (fun a ↦ idx a = q), coef a := by
  classical
  rw [map_sum, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul]
  show coef a * standardCoordinateEquiv (K := K) (κ := κ) _ q = _
  rw [standardCoordinateEquiv_pure_single]
  split_ifs with h
  · subst h; simp
  · simp

end StandardBasis

/-- The tensor product of two finite coordinate spaces is the coordinate space on pairs. -/
noncomputable def coordinateTensorEquiv {α : Type v} {β : Type w}
    [Finite α] [Finite β] :
    TensorProduct K (α → K) (β → K) ≃ₗ[K] (α × β → K) :=
  ((Pi.basisFun K α).tensorProduct (Pi.basisFun K β)).equivFun

@[simp] theorem coordinateTensorEquiv_single_tmul_single
    {α : Type v} {β : Type w} [Finite α] [Finite β]
    [DecidableEq α] [DecidableEq β] (a : α) (b : β) :
    coordinateTensorEquiv (K := K)
        (Pi.single a 1 ⊗ₜ[K] Pi.single b 1) =
      Pi.single (a, b) 1 := by
  rw [← Pi.basisFun_apply, ← Pi.basisFun_apply]
  ext p
  rcases p with ⟨a', b'⟩
  simp only [coordinateTensorEquiv, Module.Basis.equivFun_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, Pi.basisFun_repr, Pi.single_apply,
    Prod.mk.injEq]
  by_cases ha : a' = a <;> by_cases hb : b' = b <;> simp [ha, hb]

/-- Reindexing a standard basis vector carries its index through the equivalence. -/
@[simp] theorem funCongrLeft_symm_single
    {α : Type v} {β : Type w} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a : α) (r : K) :
    LinearEquiv.funCongrLeft K K e.symm (Pi.single a r) =
      Pi.single (e a) r := by
  ext b
  simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  by_cases h : b = e a
  · subst b
    simp
  · have h' : e.symm b ≠ a := by
      intro hba
      apply h
      rw [← e.apply_symm_apply b, hba]
    simp [h, h']

/-! ## Legwise relabelling of standard coordinates

An equivalence of index types on every leg induces a legwise isomorphism of the corresponding
coordinate tensors that merely permutes standard basis vectors.  This is the only kind of legwise
isomorphism the concrete examples need, and it is what carries an explicit coordinate certificate
to an explicit coordinate certificate. -/

section Relabel

variable {ι : Leg → Type*} {ι' : Leg → Type*}

/-- Relabel the standard coordinates of leg `c` along an equivalence of index types. -/
noncomputable def relabelLegEquiv (K : Type u) [CommSemiring K] (ρ : ∀ c, ι c ≃ ι' c) (c : Leg) :
    CoordinateSpace K ι c ≃ₗ[K] CoordinateSpace K ι' c :=
  LinearEquiv.funCongrLeft K K (ρ c).symm

/-- Coefficients transport along a legwise relabelling by pulling the index back through it.  This
is `standardCoordinateEquiv_map_funLeft` for the bijective case, and it is what lets a support
formula proved for one presentation of a tensor be read off for every relabelling of it. -/
theorem standardCoordinateEquiv_congr_relabel [∀ c, Finite (ι c)] [∀ c, Finite (ι' c)]
    (ρ : ∀ c, ι c ≃ ι' c) (T : Tensor3 K (CoordinateSpace K ι)) (p : ∀ c, ι' c) :
    standardCoordinateEquiv (K := K) (κ := ι')
        (PiTensorProduct.congr (relabelLegEquiv K ρ) T) p =
      standardCoordinateEquiv (K := K) (κ := ι) T (fun c ↦ (ρ c).symm (p c)) :=
  standardCoordinateEquiv_map_funLeft (K := K) (κ := ι) (κ' := ι')
    (fun c ↦ (ρ c).symm) T p

/-- A legwise relabelling carries the pure basis tensor at the triple `(x, y, z)` to the pure basis
tensor at the relabelled triple. -/
theorem congr_relabelLegEquiv_pure [∀ c, DecidableEq (ι c)] [∀ c, DecidableEq (ι' c)]
    (ρ : ∀ c, ι c ≃ ι' c) (x : ι .X) (y : ι .Y) (z : ι .Z) :
    PiTensorProduct.congr (relabelLegEquiv K ρ)
        (pure (K := K) (ofLegs (V := CoordinateSpace K ι)
          (Pi.single x 1) (Pi.single y 1) (Pi.single z 1))) =
      pure (K := K) (ofLegs (V := CoordinateSpace K ι')
        (Pi.single (ρ .X x) 1) (Pi.single (ρ .Y y) 1) (Pi.single (ρ .Z z) 1)) := by
  rw [PiTensorProduct.congr_tprod]
  congr 1
  funext c
  cases c <;>
    exact funCongrLeft_symm_single (K := K) (ρ _) _ 1

end Relabel

end AlgebraicComplexity.Tensor
