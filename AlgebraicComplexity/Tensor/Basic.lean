/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.BasicDefs

/-!
# Three-legged tensors

This file re-exports the typed tensor representation from `Tensor/BasicDefs.lean` and develops
its elementary three-leg, pure-tensor, map, and permutation calculus.  A tensor has three named
legs and is represented by Mathlib's finite `PiTensorProduct`.  Using a named finite index makes
coordinate permutations independent of a particular parenthesization of binary tensor products.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

/-- Expand a finite product over the three named tensor legs. -/
theorem prod_leg {M : Type*} [CommMonoid M] (f : Leg → M) :
    ∏ i, f i = f .X * f .Y * f .Z := by
  rw [show (Finset.univ : Finset Leg) = {.X, .Y, .Z} by decide]
  simp [mul_assoc]

/-- Expand a finite sum over the three named tensor legs. -/
theorem sum_leg {M : Type*} [AddCommMonoid M] (f : Leg → M) :
    ∑ i, f i = f .X + f .Y + f .Z := by
  rw [show (Finset.univ : Finset Leg) = {.X, .Y, .Z} by decide]
  simp [add_assoc]

/-- Two nondependent three-leg families assembled with `ofLegs` are equal exactly when their
three named components are equal.  This is the convenient injectivity rule for finite support
calculations whose block alphabet is shared by all legs. -/
@[simp] theorem ofLegs_eq_ofLegs_iff {A : Type v}
    (x y z x' y' z' : A) :
    ofLegs (V := fun _ : Leg ↦ A) x y z = ofLegs x' y' z' ↔
      x = x' ∧ y = y' ∧ z = z' := by
  constructor
  · intro h
    exact ⟨congrFun h .X, congrFun h .Y, congrFun h .Z⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Applying the `ofLegs`-assembled family of functions `fx`, `fy`, `fz` pointwise to a
dependent family `x` yields the family assembled from the three images. -/
theorem ofLegs_apply {V : Leg → Type v} {W : Leg → Type w}
    (fx : V .X → W .X) (fy : V .Y → W .Y) (fz : V .Z → W .Z)
    (x : ∀ c, V c) :
    (fun c ↦ (ofLegs (V := fun i ↦ V i → W i) fx fy fz c) (x c)) =
      ofLegs (V := W) (fx (x .X)) (fy (x .Y)) (fz (x .Z)) := by
  funext c
  cases c <;> rfl

/-- Overwriting the `Y` component of `ofLegs x y₀ z` with `y` yields `ofLegs x y z`. -/
@[simp] theorem update_ofLegs_Y {V : Leg → Type v}
    (x : V .X) (y₀ y : V .Y) (z : V .Z) :
    Function.update (ofLegs x y₀ z) .Y y = ofLegs x y z := by
  funext c
  cases c <;> rfl

/-- Overwriting the `Z` component of `ofLegs x y z₀` with `z` yields `ofLegs x y z`. -/
@[simp] theorem update_ofLegs_Z {V : Leg → Type v}
    (x : V .X) (y : V .Y) (z₀ z : V .Z) :
    Function.update (ofLegs x y z₀) .Z z = ofLegs x y z := by
  funext c
  cases c <;> rfl

section

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- Applying an `ofLegs`-assembled family of linear maps componentwise inside a pure tensor
gives the pure tensor assembled from the three images. -/
@[simp] theorem pure_ofLegs_linearMap_apply
    (fx : V .X →ₗ[K] W .X) (fy : V .Y →ₗ[K] W .Y) (fz : V .Z →ₗ[K] W .Z)
    (x : ∀ c, V c) :
    pure (K := K)
        (fun c ↦ (ofLegs (V := fun i ↦ V i →ₗ[K] W i) fx fy fz c) (x c)) =
      pure (K := K) (ofLegs (V := W) (fx (x .X)) (fy (x .Y)) (fz (x .Z))) := by
  congr 1
  funext c
  cases c <;> rfl

/-- A pure tensor whose `X` component is zero is the zero tensor. -/
@[simp] theorem pure_ofLegs_zero_X (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs (0 : V .X) y z) = 0 := by
  exact (PiTensorProduct.tprod K).map_coord_zero .X rfl

/-- A pure tensor whose `Y` component is zero is the zero tensor. -/
@[simp] theorem pure_ofLegs_zero_Y (x : V .X) (z : V .Z) :
    pure (K := K) (ofLegs x (0 : V .Y) z) = 0 := by
  exact (PiTensorProduct.tprod K).map_coord_zero .Y rfl

/-- A pure tensor whose `Z` component is zero is the zero tensor. -/
@[simp] theorem pure_ofLegs_zero_Z (x : V .X) (y : V .Y) :
    pure (K := K) (ofLegs x y (0 : V .Z)) = 0 := by
  exact (PiTensorProduct.tprod K).map_coord_zero .Z rfl

/-- A pure tensor is additive in its `X` component: a sum in the `X` leg expands to a sum of
two pure tensors. -/
@[simp] theorem pure_ofLegs_add_X (x₁ x₂ : V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs (x₁ + x₂) y z) =
      pure (K := K) (ofLegs x₁ y z) + pure (K := K) (ofLegs x₂ y z) := by
  simpa only [update_ofLegs_X] using
    (PiTensorProduct.tprod K).map_update_add (ofLegs (0 : V .X) y z) .X x₁ x₂

/-- A pure tensor is additive in its `Y` component: a sum in the `Y` leg expands to a sum of
two pure tensors. -/
@[simp] theorem pure_ofLegs_add_Y (x : V .X) (y₁ y₂ : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs x (y₁ + y₂) z) =
      pure (K := K) (ofLegs x y₁ z) + pure (K := K) (ofLegs x y₂ z) := by
  simpa only [update_ofLegs_Y] using
    (PiTensorProduct.tprod K).map_update_add (ofLegs x (0 : V .Y) z) .Y y₁ y₂

/-- A pure tensor is additive in its `Z` component: a sum in the `Z` leg expands to a sum of
two pure tensors. -/
@[simp] theorem pure_ofLegs_add_Z (x : V .X) (y : V .Y) (z₁ z₂ : V .Z) :
    pure (K := K) (ofLegs x y (z₁ + z₂)) =
      pure (K := K) (ofLegs x y z₁) + pure (K := K) (ofLegs x y z₂) := by
  simpa only [update_ofLegs_Z] using
    (PiTensorProduct.tprod K).map_update_add (ofLegs x y (0 : V .Z)) .Z z₁ z₂

/-- A scalar factor on the `Y` component of a pure tensor pulls out as a scalar multiple of the
whole tensor. -/
@[simp] theorem pure_ofLegs_smul_Y (a : K) (x : V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs x (a • y) z) = a • pure (K := K) (ofLegs x y z) := by
  simpa only [update_ofLegs_Y] using
    (PiTensorProduct.tprod K).map_update_smul (ofLegs x (0 : V .Y) z) .Y a y

/-- A scalar factor on the `Z` component of a pure tensor pulls out as a scalar multiple of the
whole tensor. -/
@[simp] theorem pure_ofLegs_smul_Z (a : K) (x : V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs x y (a • z)) = a • pure (K := K) (ofLegs x y z) := by
  simpa only [update_ofLegs_Z] using
    (PiTensorProduct.tprod K).map_update_smul (ofLegs x y (0 : V .Z)) .Z a z

/-- Distribute a finite sum in the `X` leg of a pure tensor. -/
theorem pure_ofLegs_finset_sum_X {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs (∑ a ∈ s, f a) y z) =
      ∑ a ∈ s, pure (K := K) (ofLegs (f a) y z) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Distribute a finite sum in the `Y` leg of a pure tensor. -/
theorem pure_ofLegs_finset_sum_Y {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → V .Y) (x : V .X) (z : V .Z) :
    pure (K := K) (ofLegs x (∑ a ∈ s, f a) z) =
      ∑ a ∈ s, pure (K := K) (ofLegs x (f a) z) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Distribute a finite sum in the `Z` leg of a pure tensor. -/
theorem pure_ofLegs_finset_sum_Z {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → V .Z) (x : V .X) (y : V .Y) :
    pure (K := K) (ofLegs x y (∑ a ∈ s, f a)) =
      ∑ a ∈ s, pure (K := K) (ofLegs x y (f a)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Fintype form of `pure_ofLegs_finset_sum_X`. -/
theorem pure_ofLegs_fintype_sum_X {α : Type*} [Fintype α]
    (f : α → V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs (∑ a, f a) y z) =
      ∑ a, pure (K := K) (ofLegs (f a) y z) := by
  classical
  exact pure_ofLegs_finset_sum_X Finset.univ f y z

/-- Fintype form of `pure_ofLegs_finset_sum_Y`. -/
theorem pure_ofLegs_fintype_sum_Y {α : Type*} [Fintype α]
    (f : α → V .Y) (x : V .X) (z : V .Z) :
    pure (K := K) (ofLegs x (∑ a, f a) z) =
      ∑ a, pure (K := K) (ofLegs x (f a) z) := by
  classical
  exact pure_ofLegs_finset_sum_Y Finset.univ f x z

/-- Fintype form of `pure_ofLegs_finset_sum_Z`. -/
theorem pure_ofLegs_fintype_sum_Z {α : Type*} [Fintype α]
    (f : α → V .Z) (x : V .X) (y : V .Y) :
    pure (K := K) (ofLegs x y (∑ a, f a)) =
      ∑ a, pure (K := K) (ofLegs x y (f a)) := by
  classical
  exact pure_ofLegs_finset_sum_Z Finset.univ f x y

/-- Apply one linear map on each tensor leg. -/
abbrev map (f : ∀ i, V i →ₗ[K] W i) : Tensor3 K V →ₗ[K] Tensor3 K W :=
  PiTensorProduct.map f

/-- The legwise map `map f` sends the pure tensor of the family `x` to the pure tensor of the
componentwise images `f i (x i)`. -/
@[simp] theorem map_pure (f : ∀ i, V i →ₗ[K] W i) (x : ∀ i, V i) :
    map f (pure (K := K) x) = pure (K := K) (fun i ↦ f i (x i)) := by
  exact PiTensorProduct.map_tprod f x

/-- If one leg map is zero, the induced tensor map annihilates every tensor. -/
theorem map_eq_zero_of_coord (f : ∀ i, V i →ₗ[K] W i) (T : Tensor3 K V)
    (c : Leg) (hc : f c = 0) : map f T = 0 := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    rw [LinearMap.map_smul, map_pure]
    have hzero : (fun i ↦ f i (x i)) c = 0 := by simp [hc]
    change a • (PiTensorProduct.tprod K) (fun i ↦ f i (x i)) = 0
    rw [(PiTensorProduct.tprod K).map_coord_zero c hzero, smul_zero]
  · intro T₁ T₂ h₁ h₂
    simp [h₁, h₂]

/-- If the `X` leg map is zero, the induced map on tensors sends every tensor to zero. -/
@[simp] theorem map_ofLegs_zero_X (fy : V .Y →ₗ[K] W .Y)
    (fz : V .Z →ₗ[K] W .Z) (T : Tensor3 K V) :
    map (ofLegs (0 : V .X →ₗ[K] W .X) fy fz) T = 0 :=
  map_eq_zero_of_coord _ T .X rfl

/-- If the `Y` leg map is zero, the induced map on tensors sends every tensor to zero. -/
@[simp] theorem map_ofLegs_zero_Y (fx : V .X →ₗ[K] W .X)
    (fz : V .Z →ₗ[K] W .Z) (T : Tensor3 K V) :
    map (ofLegs fx (0 : V .Y →ₗ[K] W .Y) fz) T = 0 :=
  map_eq_zero_of_coord _ T .Y rfl

/-- If the `Z` leg map is zero, the induced map on tensors sends every tensor to zero. -/
@[simp] theorem map_ofLegs_zero_Z (fx : V .X →ₗ[K] W .X)
    (fy : V .Y →ₗ[K] W .Y) (T : Tensor3 K V) :
    map (ofLegs fx fy (0 : V .Z →ₗ[K] W .Z)) T = 0 :=
  map_eq_zero_of_coord _ T .Z rfl

/-- The induced tensor map is additive in its `X` leg map. -/
theorem map_ofLegs_add_X (f₁ f₂ : V .X →ₗ[K] W .X)
    (fy : V .Y →ₗ[K] W .Y) (fz : V .Z →ₗ[K] W .Z) (T : Tensor3 K V) :
    map (ofLegs (f₁ + f₂) fy fz) T =
      map (ofLegs f₁ fy fz) T + map (ofLegs f₂ fy fz) T := by
  have h := PiTensorProduct.map_update_add
    (f := ofLegs (0 : V .X →ₗ[K] W .X) fy fz) .X f₁ f₂
  simpa using LinearMap.congr_fun h T

/-- The induced tensor map is additive in its `Y` leg map. -/
theorem map_ofLegs_add_Y (fx : V .X →ₗ[K] W .X)
    (f₁ f₂ : V .Y →ₗ[K] W .Y) (fz : V .Z →ₗ[K] W .Z) (T : Tensor3 K V) :
    map (ofLegs fx (f₁ + f₂) fz) T =
      map (ofLegs fx f₁ fz) T + map (ofLegs fx f₂ fz) T := by
  have h := PiTensorProduct.map_update_add
    (f := ofLegs fx (0 : V .Y →ₗ[K] W .Y) fz) .Y f₁ f₂
  simpa using LinearMap.congr_fun h T

/-- The induced tensor map is additive in its `Z` leg map. -/
theorem map_ofLegs_add_Z (fx : V .X →ₗ[K] W .X)
    (fy : V .Y →ₗ[K] W .Y) (f₁ f₂ : V .Z →ₗ[K] W .Z)
    (T : Tensor3 K V) :
    map (ofLegs fx fy (f₁ + f₂)) T =
      map (ofLegs fx fy f₁) T + map (ofLegs fx fy f₂) T := by
  have h := PiTensorProduct.map_update_add
    (f := ofLegs fx fy (0 : V .Z →ₗ[K] W .Z)) .Z f₁ f₂
  simpa using LinearMap.congr_fun h T

/-- The legwise map induced by the identity on every leg is the identity on tensors. -/
@[simp] theorem map_id :
    map (fun i ↦ LinearMap.id (R := K) (M := V i)) = LinearMap.id := by
  exact PiTensorProduct.map_id

/-- Legwise mapping is functorial: the map induced by the compositions `g i ∘ₗ f i` (first `f`
from `V` to `W`, then `g` from `W` to `U`) is the composition `map g ∘ₗ map f`. -/
theorem map_comp {U : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    (f : ∀ i, V i →ₗ[K] W i) (g : ∀ i, W i →ₗ[K] U i) :
    map (fun i ↦ g i ∘ₗ f i) = map g ∘ₗ map f := by
  change PiTensorProduct.map (fun i ↦ g i ∘ₗ f i) =
    PiTensorProduct.map g ∘ₗ PiTensorProduct.map f
  exact PiTensorProduct.map_comp g f

/-- Composition of two legwise maps, in applied form.  `Tensor.map_comp` states the same fact for
the maps themselves; this is the version that rewrites inside a tensor expression. -/
theorem map_map_comp {A₁ A₂ A₃ : Leg → Type*}
    [∀ c, AddCommMonoid (A₁ c)] [∀ c, Module K (A₁ c)]
    [∀ c, AddCommMonoid (A₂ c)] [∀ c, Module K (A₂ c)]
    [∀ c, AddCommMonoid (A₃ c)] [∀ c, Module K (A₃ c)]
    (f : ∀ c, A₁ c →ₗ[K] A₂ c) (g : ∀ c, A₂ c →ₗ[K] A₃ c) (T : Tensor3 K A₁) :
    map g (map f T) = map (fun c ↦ g c ∘ₗ f c) T := by
  rw [map_comp]
  rfl

/-- Reindex the tensor legs by an orientation. -/
abbrev permute (e : Orientation) :
    Tensor3 K V ≃ₗ[K] Tensor3 K (fun i ↦ V (e.symm i)) :=
  PiTensorProduct.reindex K V e

/-- Permuting a pure tensor by the orientation `e` gives the pure tensor whose component on
leg `i` is the original component on leg `e.symm i`. -/
@[simp] theorem permute_pure (e : Orientation) (x : ∀ i, V i) :
    permute e (pure (K := K) x) = pure (K := K) (fun i ↦ x (e.symm i)) := by
  exact PiTensorProduct.reindex_tprod e x

/-- Permuting by the identity orientation is the identity equivalence on tensors. -/
@[simp] theorem permute_refl :
    permute (Equiv.refl Leg) = LinearEquiv.refl K (Tensor3 K V) := by
  exact PiTensorProduct.reindex_refl

/-- Permuting first by `e₁` and then by `e₂` equals permuting once by the composite
orientation `e₁.trans e₂`. -/
theorem permute_trans (e₁ e₂ : Orientation) :
    (permute (K := K) (V := V) e₁).trans
        (permute (K := K) (V := fun i ↦ V (e₁.symm i)) e₂) =
      permute (K := K) (V := V) (e₁.trans e₂) := by
  exact PiTensorProduct.reindex_trans e₁ e₂

end

section Ring

variable {K : Type u} [CommRing K]
variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Negating the `X` component of a pure tensor negates the whole tensor. -/
@[simp] theorem pure_ofLegs_neg_X (x : V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs (-x) y z) = -pure (K := K) (ofLegs x y z) := by
  simpa only [neg_one_smul] using pure_ofLegs_smul_X (K := K) (-1 : K) x y z

/-- Negating the `Y` component of a pure tensor negates the whole tensor. -/
@[simp] theorem pure_ofLegs_neg_Y (x : V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs x (-y) z) = -pure (K := K) (ofLegs x y z) := by
  simpa only [neg_one_smul] using pure_ofLegs_smul_Y (K := K) (-1 : K) x y z

/-- Negating the `Z` component of a pure tensor negates the whole tensor. -/
@[simp] theorem pure_ofLegs_neg_Z (x : V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs x y (-z)) = -pure (K := K) (ofLegs x y z) := by
  simpa only [neg_one_smul] using pure_ofLegs_smul_Z (K := K) (-1 : K) x y z

end Ring

end AlgebraicComplexity.Tensor
