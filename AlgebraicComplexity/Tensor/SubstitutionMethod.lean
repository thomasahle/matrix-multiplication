/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Concise

/-!
# The substitution method for tensor-rank lower bounds

This file provides the classical one-step substitution lemma used to prove tensor-rank lower
bounds beyond flattening, in the certificate-friendly direction: from a constructive rank
certificate `RankLE r T` it produces a rank certificate `RankLE (r - 1)` for a tensor obtained by
substituting a generic value into one variable of one leg.

## Objects

* `substProj φ v`: for a covector `φ` on a module `M` and a vector `v`, the linear map
  `w ↦ w - φ w • v`.  When `φ v = 1` this is the projection onto the hyperplane `ker φ` that
  kills the substitution direction `v`; it implements the substitution of the value
  `-(φ w) v`-style corrections into the distinguished variable.  It is a statement about a single
  module, so the leg names `substProjX`, `substProjY`, `substProjZ` are abbreviations for it and
  `Examples/WinogradLowerBound.lean` reuses it verbatim on `Matrix (Fin 2) (Fin 2) K`.
* `substituteX φ v T` (and mirrors): the tensor obtained from `T` by applying `substProjX φ v` on
  the `X` leg and the identity on the two other legs.

## Principal results

* `contractX_map`, `contractY_map`, `contractZ_map`: contracting a legwise-mapped tensor equals
  mapping a contraction against composed covectors; specializations
  `contract{X,Y,Z}_substitute{X,Y,Z}` compute contractions of substituted tensors.
* `RankLE.exists_substituteX` (and mirrors): the substitution step.  If `T` has a rank
  certificate of length `r` and the covector `φ` on the `X` leg detects `T` through some product
  contraction (`φ (contractX fy fz T) ≠ 0`), then there is a vector `v` with `φ v = 1` such that
  the substituted tensor `substituteX φ v T` has a rank certificate of length `r - 1`.
* `rank_lower_of_substituteX` (and mirrors): the packaged lower-bound step for `rank`: a uniform
  lower bound `s` on the rank of every unit-covector substitution yields `s + 1 ≤ rank T`.

## Layer placement and strategy

This is a layer-1 tensor-algebra module.  It imports only `Tensor.Concise` (for the dual
contractions) and mentions no matrix-multiplication construction or numerical bound.

Proof sketch for the substitution step: pick a decomposition `T = ∑ l, x_l ⊗ y_l ⊗ z_l` of
length at most `r`.  Since `φ (contractX fy fz T) = ∑ l, fy (y_l) * fz (z_l) * φ (x_l)` is
nonzero, some term has `φ (x_l) ≠ 0`; normalize it to `v := (φ (x_l))⁻¹ • x_l`, so `φ v = 1`.
The projection `substProjX φ v` annihilates `x_l` and is applied termwise to the decomposition,
so exactly one pure term dies and at most `r - 1` terms remain.  This is the classical
substitution method of the matrix-multiplication lower bounds of Winograd [*On multiplication of
2×2 matrices*, Linear Algebra Appl. 4 (1971)] and Hopcroft–Kerr [*On minimizing the number of
multiplications necessary for matrix multiplication*, SIAM J. Appl. Math. 20 (1971)].

## Non-goals

The nonvanishing hypothesis is stated against a rank-one (product) covector on the two untouched
legs, which is what explicit coordinate certificates provide; the marginally more general form
against an arbitrary covector of the flattened two-leg space is deliberately left to future work.
Iterated substitution bookkeeping (as needed for the full Hopcroft–Kerr/Winograd `2 × 2` bound of
seven) is likewise left to downstream work; this file provides the single reusable step.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

section Projection

variable {K : Type u} [CommSemiring K]
section Module

variable {M : Type v} [AddCommGroup M] [Module K M]

/-- The **substitution projection** of a module: `w ↦ w - φ w • v`.  When `φ v = 1` this is the
projection onto the hyperplane `ker φ` along the substitution direction `v`; it implements the
substitution of the value `-(φ w) v`-style corrections into the distinguished variable.

This is a statement about a single module, not about tensors: the three leg-specific names
`substProjX`, `substProjY`, `substProjZ` below are reducible abbreviations for it, and
`Examples/WinogradLowerBound.lean` reuses it for the trilinear-form route. -/
def substProj (φ : M →ₗ[K] K) (v : M) : M →ₗ[K] M :=
  LinearMap.id - φ.smulRight v

/-- Evaluation formula for the substitution projection. -/
@[simp] theorem substProj_apply (φ : M →ₗ[K] K) (v w : M) :
    substProj φ v w = w - φ w • v := by
  simp [substProj]

/-- The substitution projection kills the substitution direction: `substProj φ v v = 0` when
`φ v = 1`. -/
theorem substProj_apply_self {φ : M →ₗ[K] K} {v : M} (hv : φ v = 1) :
    substProj φ v v = 0 := by
  simp [hv]

/-- The substitution projection fixes the hyperplane `ker φ` pointwise. -/
theorem substProj_apply_of_ker {φ : M →ₗ[K] K} (v : M) {w : M} (hw : φ w = 0) :
    substProj φ v w = w := by
  simp [hw]

end Module

variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- The substitution projection on the `X` leg: `w ↦ w - φ w • v`, an abbreviation for the
module-level `substProj`. -/
abbrev substProjX (φ : V .X →ₗ[K] K) (v : V .X) : V .X →ₗ[K] V .X := substProj φ v

/-- Evaluation formula for the `X`-leg substitution projection. -/
@[simp] theorem substProjX_apply (φ : V .X →ₗ[K] K) (v w : V .X) :
    substProjX φ v w = w - φ w • v := substProj_apply φ v w

/-- The substitution projection fixes the hyperplane `ker φ` pointwise. -/
theorem substProjX_apply_of_ker {φ : V .X →ₗ[K] K} (v : V .X) {w : V .X} (hw : φ w = 0) :
    substProjX φ v w = w := substProj_apply_of_ker v hw

/-- The substitution projection on the `Y` leg: `w ↦ w - φ w • v`. -/
abbrev substProjY (φ : V .Y →ₗ[K] K) (v : V .Y) : V .Y →ₗ[K] V .Y := substProj φ v

/-- Evaluation formula for the `Y`-leg substitution projection. -/
@[simp] theorem substProjY_apply (φ : V .Y →ₗ[K] K) (v w : V .Y) :
    substProjY φ v w = w - φ w • v := substProj_apply φ v w

/-- The substitution projection fixes the hyperplane `ker φ` pointwise. -/
theorem substProjY_apply_of_ker {φ : V .Y →ₗ[K] K} (v : V .Y) {w : V .Y} (hw : φ w = 0) :
    substProjY φ v w = w := substProj_apply_of_ker v hw

/-- The substitution projection on the `Z` leg: `w ↦ w - φ w • v`. -/
abbrev substProjZ (φ : V .Z →ₗ[K] K) (v : V .Z) : V .Z →ₗ[K] V .Z := substProj φ v

/-- Evaluation formula for the `Z`-leg substitution projection. -/
@[simp] theorem substProjZ_apply (φ : V .Z →ₗ[K] K) (v w : V .Z) :
    substProjZ φ v w = w - φ w • v := substProj_apply φ v w

/-- The substitution projection fixes the hyperplane `ker φ` pointwise. -/
theorem substProjZ_apply_of_ker {φ : V .Z →ₗ[K] K} (v : V .Z) {w : V .Z} (hw : φ w = 0) :
    substProjZ φ v w = w := substProj_apply_of_ker v hw

/-- Substitute on the `X` leg: apply the substitution projection `substProjX φ v` to the `X`
leg of `T` and the identity to the `Y` and `Z` legs.  The source `T` restricts to the result. -/
def substituteX (φ : V .X →ₗ[K] K) (v : V .X) (T : Tensor3 K V) : Tensor3 K V :=
  map (ofLegs (substProjX φ v) LinearMap.id LinearMap.id) T

/-- Substituting on the `X` leg of a pure tensor projects its `X` component. -/
@[simp] theorem substituteX_pure (φ : V .X →ₗ[K] K) (v : V .X) (x : ∀ i, V i) :
    substituteX φ v (pure (K := K) x) =
      pure (K := K) (ofLegs (substProjX φ v (x .X)) (x .Y) (x .Z)) := by
  unfold substituteX
  rw [map_pure]
  simp

/-- The source tensor `T` restricts to its `X`-substituted image `substituteX φ v T`. -/
theorem restricts_substituteX (φ : V .X →ₗ[K] K) (v : V .X) (T : Tensor3 K V) :
    Restricts T (substituteX φ v T) :=
  ⟨ofLegs (substProjX φ v) LinearMap.id LinearMap.id, rfl⟩

/-- Substitute on the `Y` leg: apply the substitution projection `substProjY φ v` to the `Y`
leg of `T` and the identity to the `X` and `Z` legs.  The source `T` restricts to the result. -/
def substituteY (φ : V .Y →ₗ[K] K) (v : V .Y) (T : Tensor3 K V) : Tensor3 K V :=
  map (ofLegs LinearMap.id (substProjY φ v) LinearMap.id) T

/-- Substituting on the `Y` leg of a pure tensor projects its `Y` component. -/
@[simp] theorem substituteY_pure (φ : V .Y →ₗ[K] K) (v : V .Y) (x : ∀ i, V i) :
    substituteY φ v (pure (K := K) x) =
      pure (K := K) (ofLegs (x .X) (substProjY φ v (x .Y)) (x .Z)) := by
  unfold substituteY
  rw [map_pure]
  simp

/-- The source tensor `T` restricts to its `Y`-substituted image `substituteY φ v T`. -/
theorem restricts_substituteY (φ : V .Y →ₗ[K] K) (v : V .Y) (T : Tensor3 K V) :
    Restricts T (substituteY φ v T) :=
  ⟨ofLegs LinearMap.id (substProjY φ v) LinearMap.id, rfl⟩

/-- Substitute on the `Z` leg: apply the substitution projection `substProjZ φ v` to the `Z`
leg of `T` and the identity to the `X` and `Y` legs.  The source `T` restricts to the result. -/
def substituteZ (φ : V .Z →ₗ[K] K) (v : V .Z) (T : Tensor3 K V) : Tensor3 K V :=
  map (ofLegs LinearMap.id LinearMap.id (substProjZ φ v)) T

/-- Substituting on the `Z` leg of a pure tensor projects its `Z` component. -/
@[simp] theorem substituteZ_pure (φ : V .Z →ₗ[K] K) (v : V .Z) (x : ∀ i, V i) :
    substituteZ φ v (pure (K := K) x) =
      pure (K := K) (ofLegs (x .X) (x .Y) (substProjZ φ v (x .Z))) := by
  unfold substituteZ
  rw [map_pure]
  simp

/-- The source tensor `T` restricts to its `Z`-substituted image `substituteZ φ v T`. -/
theorem restricts_substituteZ (φ : V .Z →ₗ[K] K) (v : V .Z) (T : Tensor3 K V) :
    Restricts T (substituteZ φ v T) :=
  ⟨ofLegs LinearMap.id LinearMap.id (substProjZ φ v), rfl⟩

end Projection

section ProjectionRing

variable {K : Type u} [CommRing K] {M : Type v} [AddCommGroup M] [Module K M]

/-- The image of a substitution projection with a unit covector lies in `ker φ`.  Stated at the
module level, so that all three legs and the trilinear-form route share one proof. -/
theorem phi_substProj_apply {φ : M →ₗ[K] K} {v : M} (hv : φ v = 1) (w : M) :
    φ (substProj φ v w) = 0 := by
  simp [hv, smul_eq_mul]

end ProjectionRing

section Contraction

variable {K : Type u} [Field K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

/-- Contracting the `Y` and `Z` legs of a legwise-mapped tensor equals mapping the `X` leg of
the contraction of the source against the composed covectors. -/
theorem contractX_map (f : ∀ i, V i →ₗ[K] W i)
    (fy : W .Y →ₗ[K] K) (fz : W .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractX fy fz (map f T) =
      f .X (contractX (fy ∘ₗ f .Y) (fz ∘ₗ f .Z) T) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp [smul_smul]
  · intro T₁ T₂ h₁ h₂
    simp [h₁, h₂]

/-- Contracting the `X` and `Z` legs of a legwise-mapped tensor equals mapping the `Y` leg of
the contraction of the source against the composed covectors. -/
theorem contractY_map (f : ∀ i, V i →ₗ[K] W i)
    (fx : W .X →ₗ[K] K) (fz : W .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractY fx fz (map f T) =
      f .Y (contractY (fx ∘ₗ f .X) (fz ∘ₗ f .Z) T) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp [smul_smul]
  · intro T₁ T₂ h₁ h₂
    simp [h₁, h₂]

/-- Contracting the `X` and `Y` legs of a legwise-mapped tensor equals mapping the `Z` leg of
the contraction of the source against the composed covectors. -/
theorem contractZ_map (f : ∀ i, V i →ₗ[K] W i)
    (fx : W .X →ₗ[K] K) (fy : W .Y →ₗ[K] K) (T : Tensor3 K V) :
    contractZ fx fy (map f T) =
      f .Z (contractZ (fx ∘ₗ f .X) (fy ∘ₗ f .Y) T) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp [smul_smul]
  · intro T₁ T₂ h₁ h₂
    simp [h₁, h₂]

end Contraction

section ContractSubstitute

variable {K : Type u} [Field K]
variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- An `X`-retaining contraction of an `X`-substituted tensor is the substitution projection of
the corresponding contraction of the source. -/
theorem contractX_substituteX (φ : V .X →ₗ[K] K) (v : V .X)
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractX fy fz (substituteX φ v T) =
      substProjX φ v (contractX fy fz T) := by
  unfold substituteX
  rw [contractX_map]
  simp

/-- A `Y`-retaining contraction of an `X`-substituted tensor is the contraction of the source
against the covector precomposed with the substitution projection. -/
theorem contractY_substituteX (φ : V .X →ₗ[K] K) (v : V .X)
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractY fx fz (substituteX φ v T) =
      contractY (fx ∘ₗ substProjX φ v) fz T := by
  unfold substituteX
  rw [contractY_map]
  simp

/-- A `Z`-retaining contraction of an `X`-substituted tensor is the contraction of the source
against the covector precomposed with the substitution projection. -/
theorem contractZ_substituteX (φ : V .X →ₗ[K] K) (v : V .X)
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (T : Tensor3 K V) :
    contractZ fx fy (substituteX φ v T) =
      contractZ (fx ∘ₗ substProjX φ v) fy T := by
  unfold substituteX
  rw [contractZ_map]
  simp

/-- An `X`-retaining contraction of a `Y`-substituted tensor is the contraction of the source
against the covector precomposed with the substitution projection. -/
theorem contractX_substituteY (φ : V .Y →ₗ[K] K) (v : V .Y)
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractX fy fz (substituteY φ v T) =
      contractX (fy ∘ₗ substProjY φ v) fz T := by
  unfold substituteY
  rw [contractX_map]
  simp

/-- A `Y`-retaining contraction of a `Y`-substituted tensor is the substitution projection of
the corresponding contraction of the source. -/
theorem contractY_substituteY (φ : V .Y →ₗ[K] K) (v : V .Y)
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractY fx fz (substituteY φ v T) =
      substProjY φ v (contractY fx fz T) := by
  unfold substituteY
  rw [contractY_map]
  simp

/-- A `Z`-retaining contraction of a `Y`-substituted tensor is the contraction of the source
against the covector precomposed with the substitution projection. -/
theorem contractZ_substituteY (φ : V .Y →ₗ[K] K) (v : V .Y)
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (T : Tensor3 K V) :
    contractZ fx fy (substituteY φ v T) =
      contractZ fx (fy ∘ₗ substProjY φ v) T := by
  unfold substituteY
  rw [contractZ_map]
  simp

/-- An `X`-retaining contraction of a `Z`-substituted tensor is the contraction of the source
against the covector precomposed with the substitution projection. -/
theorem contractX_substituteZ (φ : V .Z →ₗ[K] K) (v : V .Z)
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractX fy fz (substituteZ φ v T) =
      contractX fy (fz ∘ₗ substProjZ φ v) T := by
  unfold substituteZ
  rw [contractX_map]
  simp

/-- A `Y`-retaining contraction of a `Z`-substituted tensor is the contraction of the source
against the covector precomposed with the substitution projection. -/
theorem contractY_substituteZ (φ : V .Z →ₗ[K] K) (v : V .Z)
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractY fx fz (substituteZ φ v T) =
      contractY fx (fz ∘ₗ substProjZ φ v) T := by
  unfold substituteZ
  rw [contractY_map]
  simp

/-- A `Z`-retaining contraction of a `Z`-substituted tensor is the substitution projection of
the corresponding contraction of the source. -/
theorem contractZ_substituteZ (φ : V .Z →ₗ[K] K) (v : V .Z)
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (T : Tensor3 K V) :
    contractZ fx fy (substituteZ φ v T) =
      substProjZ φ v (contractZ fx fy T) := by
  unfold substituteZ
  rw [contractZ_map]
  simp

end ContractSubstitute

section Substitution

variable {K : Type u} [Field K]
variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- The substitution step on the `X` leg, in the certificate-friendly direction.

If `T` has a rank certificate of length at most `r` and the covector `φ` on the `X` leg detects
`T` through a product contraction of the other two legs (`φ (contractX fy fz T) ≠ 0`), then
there is a substitution direction `v` with `φ v = 1` such that the substituted tensor
`substituteX φ v T` has a rank certificate of length at most `r - 1`.

Proof sketch: fix a decomposition `T = ∑ l, x_l ⊗ y_l ⊗ z_l` of length at most `r`.  Then
`φ (contractX fy fz T) = ∑ l, (fy y_l * fz z_l) • φ x_l`, so nonvanishing forces `φ (x_l) ≠ 0`
for some term `l`; set `v := (φ x_l)⁻¹ • x_l`, so `φ v = 1`.  The projection `substProjX φ v`
annihilates `x_l`, so applying the substitution termwise to the decomposition kills exactly the
`l`-th pure term and leaves an explicit decomposition of the substituted tensor with at most
`r - 1` terms.  This is the classical substitution step of Winograd (1971) and
Hopcroft–Kerr (1971). -/
theorem RankLE.exists_substituteX {r : ℕ} {T : Tensor3 K V} (hT : RankLE r T)
    (φ : V .X →ₗ[K] K) {fy : V .Y →ₗ[K] K} {fz : V .Z →ₗ[K] K}
    (hslice : φ (contractX fy fz T) ≠ 0) :
    ∃ v : V .X, φ v = 1 ∧ RankLE (r - 1) (substituteX φ v T) := by
  classical
  obtain ⟨terms, hlen, rfl⟩ := hT
  have hex : ∃ x ∈ terms, φ (x .X) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hslice
    rw [map_list_sum, map_list_sum, List.map_map, List.map_map]
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp [hall x hx]
  obtain ⟨x₀, hmem, hφ⟩ := hex
  set v : V .X := (φ (x₀ .X))⁻¹ • x₀ .X with hvdef
  have hv1 : φ v = 1 := by
    rw [hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hφ]
  refine ⟨v, hv1, ?_⟩
  have hvkill : substProjX φ v (x₀ .X) = 0 := by
    rw [substProjX_apply, hvdef, smul_smul, mul_inv_cancel₀ hφ, one_smul, sub_self]
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
  refine ⟨(s ++ t).map (fun x ↦ ofLegs (substProjX φ v (x .X)) (x .Y) (x .Z)), ?_, ?_⟩
  · simp only [List.length_map, List.length_append, List.length_cons] at hlen ⊢
    omega
  · unfold substituteX
    rw [map_list_sum, List.map_map, List.map_map]
    have hfun : (Tensor.map (ofLegs (substProjX φ v) LinearMap.id LinearMap.id) ∘ pure (K := K)) =
        (pure (K := K) ∘ fun x : ∀ i, V i ↦
          ofLegs (substProjX φ v (x .X)) (x .Y) (x .Z)) := by
      funext x
      simp
    rw [hfun, ← List.map_map, ← List.map_map]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    rw [hvkill, pure_ofLegs_zero_X, zero_add]

/-- The substitution step on the `Y` leg, in the certificate-friendly direction; see
`RankLE.exists_substituteX` for the statement pattern and proof sketch. -/
theorem RankLE.exists_substituteY {r : ℕ} {T : Tensor3 K V} (hT : RankLE r T)
    (φ : V .Y →ₗ[K] K) {fx : V .X →ₗ[K] K} {fz : V .Z →ₗ[K] K}
    (hslice : φ (contractY fx fz T) ≠ 0) :
    ∃ v : V .Y, φ v = 1 ∧ RankLE (r - 1) (substituteY φ v T) := by
  classical
  obtain ⟨terms, hlen, rfl⟩ := hT
  have hex : ∃ x ∈ terms, φ (x .Y) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hslice
    rw [map_list_sum, map_list_sum, List.map_map, List.map_map]
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp [hall x hx]
  obtain ⟨x₀, hmem, hφ⟩ := hex
  set v : V .Y := (φ (x₀ .Y))⁻¹ • x₀ .Y with hvdef
  have hv1 : φ v = 1 := by
    rw [hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hφ]
  refine ⟨v, hv1, ?_⟩
  have hvkill : substProjY φ v (x₀ .Y) = 0 := by
    rw [substProjY_apply, hvdef, smul_smul, mul_inv_cancel₀ hφ, one_smul, sub_self]
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
  refine ⟨(s ++ t).map (fun x ↦ ofLegs (x .X) (substProjY φ v (x .Y)) (x .Z)), ?_, ?_⟩
  · simp only [List.length_map, List.length_append, List.length_cons] at hlen ⊢
    omega
  · unfold substituteY
    rw [map_list_sum, List.map_map, List.map_map]
    have hfun : (Tensor.map (ofLegs LinearMap.id (substProjY φ v) LinearMap.id) ∘ pure (K := K)) =
        (pure (K := K) ∘ fun x : ∀ i, V i ↦
          ofLegs (x .X) (substProjY φ v (x .Y)) (x .Z)) := by
      funext x
      simp
    rw [hfun, ← List.map_map, ← List.map_map]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    rw [hvkill, pure_ofLegs_zero_Y, zero_add]

/-- The substitution step on the `Z` leg, in the certificate-friendly direction; see
`RankLE.exists_substituteX` for the statement pattern and proof sketch. -/
theorem RankLE.exists_substituteZ {r : ℕ} {T : Tensor3 K V} (hT : RankLE r T)
    (φ : V .Z →ₗ[K] K) {fx : V .X →ₗ[K] K} {fy : V .Y →ₗ[K] K}
    (hslice : φ (contractZ fx fy T) ≠ 0) :
    ∃ v : V .Z, φ v = 1 ∧ RankLE (r - 1) (substituteZ φ v T) := by
  classical
  obtain ⟨terms, hlen, rfl⟩ := hT
  have hex : ∃ x ∈ terms, φ (x .Z) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hslice
    rw [map_list_sum, map_list_sum, List.map_map, List.map_map]
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simp [hall x hx]
  obtain ⟨x₀, hmem, hφ⟩ := hex
  set v : V .Z := (φ (x₀ .Z))⁻¹ • x₀ .Z with hvdef
  have hv1 : φ v = 1 := by
    rw [hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hφ]
  refine ⟨v, hv1, ?_⟩
  have hvkill : substProjZ φ v (x₀ .Z) = 0 := by
    rw [substProjZ_apply, hvdef, smul_smul, mul_inv_cancel₀ hφ, one_smul, sub_self]
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hmem
  refine ⟨(s ++ t).map (fun x ↦ ofLegs (x .X) (x .Y) (substProjZ φ v (x .Z))), ?_, ?_⟩
  · simp only [List.length_map, List.length_append, List.length_cons] at hlen ⊢
    omega
  · unfold substituteZ
    rw [map_list_sum, List.map_map, List.map_map]
    have hfun : (Tensor.map (ofLegs LinearMap.id LinearMap.id (substProjZ φ v)) ∘ pure (K := K)) =
        (pure (K := K) ∘ fun x : ∀ i, V i ↦
          ofLegs (x .X) (x .Y) (substProjZ φ v (x .Z))) := by
      funext x
      simp
    rw [hfun, ← List.map_map, ← List.map_map]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    rw [hvkill, pure_ofLegs_zero_Z, zero_add]

/-- Packaged substitution lower bound on the `X` leg: if the covector `φ` detects `T` through a
product contraction and every unit-covector substitution `substituteX φ v T` (over all `v` with
`φ v = 1`) has rank at least `s`, then `T` has rank at least `s + 1`.

Proof sketch: apply `RankLE.exists_substituteX` to the minimal decomposition provided by
`rank_spec`; the resulting substituted tensor has rank between `s` and `rank T - 1`, and the
detection hypothesis rules out `T = 0`, so `rank T ≥ 1` and the bound follows. -/
theorem rank_lower_of_substituteX {T : Tensor3 K V}
    (φ : V .X →ₗ[K] K) {fy : V .Y →ₗ[K] K} {fz : V .Z →ₗ[K] K}
    (hslice : φ (contractX fy fz T) ≠ 0) {s : ℕ}
    (hbound : ∀ v : V .X, φ v = 1 → s ≤ rank (substituteX φ v T)) :
    s + 1 ≤ rank T := by
  obtain ⟨v, hv, hrank⟩ := (rank_spec T).exists_substituteX φ hslice
  have h₁ : s ≤ rank T - 1 := (hbound v hv).trans (rank_le_iff.mpr hrank)
  have hT : T ≠ 0 := by
    rintro rfl
    simp at hslice
  have h₂ : 1 ≤ rank T := Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hT (rank_eq_zero.mp h0)
  omega

/-- Packaged substitution lower bound on the `Y` leg; see `rank_lower_of_substituteX`. -/
theorem rank_lower_of_substituteY {T : Tensor3 K V}
    (φ : V .Y →ₗ[K] K) {fx : V .X →ₗ[K] K} {fz : V .Z →ₗ[K] K}
    (hslice : φ (contractY fx fz T) ≠ 0) {s : ℕ}
    (hbound : ∀ v : V .Y, φ v = 1 → s ≤ rank (substituteY φ v T)) :
    s + 1 ≤ rank T := by
  obtain ⟨v, hv, hrank⟩ := (rank_spec T).exists_substituteY φ hslice
  have h₁ : s ≤ rank T - 1 := (hbound v hv).trans (rank_le_iff.mpr hrank)
  have hT : T ≠ 0 := by
    rintro rfl
    simp at hslice
  have h₂ : 1 ≤ rank T := Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hT (rank_eq_zero.mp h0)
  omega

/-- Packaged substitution lower bound on the `Z` leg; see `rank_lower_of_substituteX`. -/
theorem rank_lower_of_substituteZ {T : Tensor3 K V}
    (φ : V .Z →ₗ[K] K) {fx : V .X →ₗ[K] K} {fy : V .Y →ₗ[K] K}
    (hslice : φ (contractZ fx fy T) ≠ 0) {s : ℕ}
    (hbound : ∀ v : V .Z, φ v = 1 → s ≤ rank (substituteZ φ v T)) :
    s + 1 ≤ rank T := by
  obtain ⟨v, hv, hrank⟩ := (rank_spec T).exists_substituteZ φ hslice
  have h₁ : s ≤ rank T - 1 := (hbound v hv).trans (rank_le_iff.mpr hrank)
  have hT : T ≠ 0 := by
    rintro rfl
    simp at hslice
  have h₂ : 1 ≤ rank T := Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hT (rank_eq_zero.mp h0)
  omega

end Substitution

end AlgebraicComplexity.Tensor
