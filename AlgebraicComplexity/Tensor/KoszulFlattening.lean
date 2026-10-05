/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Rank
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Koszul flattenings and the Landsberg–Ottaviani lower-bound method

This file develops the *Koszul flattening* (also called a *Young flattening*) of a three-legged
tensor and the rank lower bound it produces.  It is the first lower-bound method in the library
that goes strictly beyond the classical one-leg flattenings of `Tensor/Concise.lean`: the
classical flattening of a tensor with an `N`-dimensional `X` leg can never certify rank more than
`N`, whereas the `p`-th Koszul flattening certifies rank up to `binom(N, p+1) * dim V_Z /
binom(N - 1, p)`, which is asymptotically `2N` for the matrix-multiplication tensors.

## The construction

Fix `p : ℕ` and write `A := V .X`.  A tensor `T ∈ A ⊗ V_Y ⊗ V_Z` induces a linear map

```text
  Φ_T^p : (⋀^p A) ⊗ V_Y*  →  (⋀^{p+1} A) ⊗ V_Z
```

determined on decomposable arguments by `Φ^p_{a ⊗ b ⊗ c} (ω ⊗ β) = β(b) • (a ∧ ω) ⊗ c` and
extended linearly in `T`.  Equivalently: contract the `Y` leg of `T` against `β`, which leaves an
element of `A ⊗ V_Z`, and then wedge the `A` factor on the left into `ω`.  That is exactly how
`koszulFlattening` is built here, out of `sliceY` (the `Y` contraction) and `wedgeLeft` (left
exterior multiplication by a vector).

## Main results

* `wedgeLeft`: left wedge multiplication `M →ₗ (⋀^p M →ₗ ⋀^{p+1} M)`, linear in the vector;
* `finrank_range_wedgeLeft_le`: the image of `a ∧ ·` on `⋀^p M` has dimension at most
  `binom (dim M - 1) p`.  This is the geometric heart of the method;
* `koszulFlattening`: the `p`-th Koszul flattening, linear in the tensor;
* `finrank_range_koszulFlattening_pure_le`: the rank-one estimate — a pure tensor has Koszul
  flattening of rank at most `binom (dim V_X - 1) p`;
* `RankLE.card_le_of_linearIndependent_koszulFlattening`: the method theorem.  A rank-`r`
  certificate for `T` caps at `r * binom (dim V_X - 1) p` the number of linearly independent
  values of `Φ_T^p` — that is, `rank (Φ_T^p) ≤ r * binom (dim V_X - 1) p`;
* `lt_rank_of_linearIndependent_koszulFlattening`: the client-facing contrapositive
  (`r * binom < #(independent values of Φ_T^p)` forces `rank T > r`).

The rank of `Φ_T^p` is expressed through linear independence of its values rather than through
`finrank (range ·)`.  The reason is purely one of elaboration cost: the target space
`⋀^{p+1} V_X ⊗ V_Z` sits at an `AddCommMonoid`/`AddCommGroup` instance diamond (the
`⋀`-factor is a submodule coercion), and every dimension lemma stated over `AddCommGroup` —
`Submodule.finrank_sup_add_finrank_inf_eq` in particular — takes prohibitively long to unify
there.  The independence form needs no such lemma and is exactly what clients use.

## Proof strategy

The only non-formal ingredient is `finrank_range_wedgeLeft_le`.  For `a ≠ 0` let `π : M → M/⟨a⟩`
be the quotient map.  Wedging is natural, so `Λ^{p+1}π (a ∧ ω) = π a ∧ Λ^p π ω = 0`; hence the
image of `a ∧ ·` sits inside `ker (Λ^{p+1} π)`.  Since `Λ^{p+1}π` is surjective, rank–nullity and
`dim ⋀^k M = binom (dim M) k` give
`dim ker = binom N (p+1) - binom (N-1) (p+1) = binom (N-1) p` by Pascal's rule.  This replaces
the usual "extend `a` to a basis and count the surviving basis bivectors" argument by a
basis-free computation, and in particular avoids choosing an ordered basis of `M`.

Everything else is formal: `Φ_T^p` is linear in `T` by construction, so all its values factor
through one auxiliary map `Ψ` out of a product `∏_j W_j` of coordinate copies of the images
`x_j ∧ ⋀^p V_X`, one per certificate term; the dimension of that product is at most
`r * binom (dim V_X - 1) p`.

## Layer placement

Layer 1 (`AlgebraicComplexity/Tensor/`).  The file mentions no named tensor and no numerical
bound; the matrix-multiplication instance lives downstream in
`AlgebraicComplexity/MatrixMultiplication/KoszulBorderRank.lean`.  It imports `Tensor/Rank` for
`RankLE` and Mathlib's exterior-power API, and deliberately does *not* import `Tensor/Concise`
or `Tensor/BorderConcise`: the Koszul bound is independent of conciseness.

## Source

J. M. Landsberg and G. Ottaviani, *New lower bounds for the border rank of matrix
multiplication*, Theory of Computing **11** (2015), 285–298 (arXiv:1112.6007), whose headline
result is `borderRank ⟨n,n,n⟩ ≥ 2n² − n`.  The Koszul/Young flattening construction `T_A^{∧p}`
and its rank-one estimate `binom (dim A − 1) p` are developed there and in J. M. Landsberg and
G. Ottaviani, *Equations for secant varieties of Veronese and other varieties*, Ann. Mat. Pura
Appl. (4) **192** (2013), 569–606.  The formalization follows the method rather than the
paper's notation; in particular the paper works over `ℂ` and phrases the estimate through
secant varieties, while everything below is stated over an arbitrary field and phrased through
explicit rank certificates.

## Non-goals and the border-rank obstruction

The *border*-rank version of the method — `borderRank T ≥ dim (range Φ_T^p) / binom (dim V_X -
1) p`, which is what Landsberg–Ottaviani actually use — is **not** proved here.  It is not a
formality, and the obstruction is worth recording precisely.

The leading-coefficient engine of `Tensor/BorderConcise.lean`
(`finrank_le_of_leadingTerm_span_shift`) reduces a border-rank certificate
`T = leading coefficient of ∑_{j<r} polynomialPure (x_j)` to the following requirement: for each
certificate term `x_j`, the polynomial paths `ε ↦ Φ^p_{polynomialPure x_j (ε)} (q)` must lie in
the span of the shifts `ε^e • u_i` of at most `binom (dim V_X - 1) p` fixed polynomial vectors
`u_i`, uniformly in `q`.  Equivalently: the `K[ε]`-module

```text
  { X(ε) ∧ ω : ω ∈ (⋀^p V_X) ⊗ K[ε] }   ⊆   (⋀^{p+1} V_X) ⊗ K[ε]
```

generated by the `X`-leg polynomial vector `X(ε)` of the term must be generated by
`binom (dim V_X - 1) p` elements over `K[ε]`.  That statement is true — `K[ε]` is a principal
ideal domain, so `X(ε) = g(ε) X'(ε)` with `X'` unimodular, `X'` extends to a `K[ε]`-basis, and
the count follows exactly as over a field — but formalizing it needs (i) Smith normal form for
the rank-one submodule `K[ε] · X(ε)`, and (ii) the base-change identification
`(⋀^k_K V_X) ⊗_K K[ε] ≅ ⋀^k_{K[ε]} (V_X ⊗_K K[ε])`, which Mathlib's `exteriorPower` API does not
currently provide.  Both are self-contained follow-on projects; the field-level statement proved
here (`finrank_range_wedgeLeft_le`) is the exact statement they would have to reproduce over
`K[ε]`.

Consequently the downstream client proves the *rank* bound `rank ⟨2,2,2⟩ ≥ 6` by the Koszul
route.  Upgrading it to `borderRank ⟨2,2,2⟩ ≥ 6` — the `n = 2` case of `2n² − n` — is exactly
the missing generation lemma above and nothing else: the flattening, its rank-one estimate and
the explicit `⟨2,2,2⟩` computation are all in place and reusable verbatim.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

/-! ### Left wedge multiplication -/

section Wedge

variable (K : Type u) [CommRing K] (M : Type v) [AddCommGroup M] [Module K M]

/-- Left exterior multiplication by a vector: `wedgeLeft K M p a` is the linear map
`ω ↦ a ∧ ω` from `⋀^p M` to `⋀^(p+1) M`, and `wedgeLeft K M p` is itself linear in `a`.

It is obtained by currying the first argument out of the canonical alternating map
`ιMulti K (p+1) : M^(p+1) → ⋀^(p+1) M` and then using the universal property of `⋀^p M`. -/
noncomputable def wedgeLeft (p : ℕ) :
    M →ₗ[K] ((⋀[K]^p M) →ₗ[K] (⋀[K]^(p + 1) M)) :=
  (exteriorPower.alternatingMapLinearEquiv (R := K) (n := p)
      (M := M) (N := (⋀[K]^(p + 1) M))).toLinearMap ∘ₗ
    (exteriorPower.ιMulti K (p + 1)).curryLeft

variable {K M}

/-- On a decomposable exterior product, `wedgeLeft` prepends the vector:
`a ∧ (v₀ ∧ ⋯ ∧ v_{p-1}) = a ∧ v₀ ∧ ⋯ ∧ v_{p-1}`. -/
@[simp] theorem wedgeLeft_apply_ιMulti (p : ℕ) (a : M) (v : Fin p → M) :
    wedgeLeft K M p a (exteriorPower.ιMulti K p v) =
      exteriorPower.ιMulti K (p + 1) (Fin.cons a v) := by
  simp only [wedgeLeft, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]
  rfl

/-- Naturality of left wedge multiplication: applying `⋀^k f` to `a ∧ ω` gives `f a ∧ (⋀^p f) ω`.

Proof sketch: both sides are linear in `ω`, so it suffices to compare them on the decomposable
generators `ιMulti K p v`, where each side is `ιMulti K (p+1)` of the tuple `Fin.cons (f a)
(f ∘ v)`. -/
theorem map_wedgeLeft {N : Type w} [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (p : ℕ)
    (a : M) (ω : ⋀[K]^p M) :
    exteriorPower.map (p + 1) f (wedgeLeft K M p a ω) =
      wedgeLeft K N p (f a) (exteriorPower.map p f ω) := by
  revert ω
  suffices h : (exteriorPower.map (p + 1) f) ∘ₗ (wedgeLeft K M p a) =
      (wedgeLeft K N p (f a)) ∘ₗ (exteriorPower.map p f) by
    intro ω
    exact congrArg (fun g ↦ g ω) h
  apply exteriorPower.linearMap_ext
  ext v
  simp [exteriorPower.map_apply_ιMulti, Fin.comp_cons]

end Wedge

/-! ### The dimension of `a ∧ ⋀^p M` -/

section WedgeFinrank

variable {K : Type u} [Field K] {M : Type v} [AddCommGroup M] [Module K M]
variable [FiniteDimensional K M]

/-- **The geometric core of the Koszul flattening method.**  For every vector `a` of an
`N`-dimensional space `M`, the image of `ω ↦ a ∧ ω : ⋀^p M → ⋀^(p+1) M` has dimension at most
`binom (N - 1) p`.

Proof sketch: for `a = 0` the map is zero.  Otherwise let `π : M → M ⧸ (K ∙ a)` be the quotient
map, so `dim (M ⧸ K∙a) = N - 1`.  Naturality of the wedge (`map_wedgeLeft`) gives
`⋀^{p+1}π (a ∧ ω) = (π a) ∧ ⋀^p π ω = 0`, so the image lies in `ker (⋀^{p+1} π)`.  The map
`⋀^{p+1} π` is surjective because `π` is, so rank–nullity together with
`dim ⋀^k M = binom (dim M) k` gives `dim ker (⋀^{p+1} π) = binom N (p+1) - binom (N-1) (p+1)`,
which is `binom (N-1) p` by Pascal's rule. -/
theorem finrank_range_wedgeLeft_le (p : ℕ) (a : M) :
    Module.finrank K (LinearMap.range (wedgeLeft K M p a)) ≤
      (Module.finrank K M - 1).choose p := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, LinearMap.range_zero, finrank_bot]
    exact Nat.zero_le _
  · set S : Submodule K M := K ∙ a with hS
    set π : M →ₗ[K] (M ⧸ S) := S.mkQ with hπ
    have hπa : π a = 0 := by
      rw [hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_span_singleton_self a
    have hle : LinearMap.range (wedgeLeft K M p a) ≤
        LinearMap.ker (exteriorPower.map (p + 1) π) := by
      rintro _ ⟨ω, rfl⟩
      rw [LinearMap.mem_ker, map_wedgeLeft, hπa, map_zero, LinearMap.zero_apply]
    have hquot : Module.finrank K (M ⧸ S) = Module.finrank K M - 1 := by
      have h1 : Module.finrank K S = 1 := finrank_span_singleton ha
      have h2 := Submodule.finrank_quotient_add_finrank S
      omega
    have hsurj : Function.Surjective (exteriorPower.map (p + 1) π) :=
      exteriorPower.map_surjective (Submodule.mkQ_surjective S)
    have hrange : Module.finrank K (LinearMap.range (exteriorPower.map (p + 1) π)) =
        (Module.finrank K M - 1).choose (p + 1) := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, exteriorPower.finrank_eq, hquot]
    have hrn := LinearMap.finrank_range_add_finrank_ker (exteriorPower.map (p + 1) π)
    rw [hrange, exteriorPower.finrank_eq] at hrn
    have hpos : 1 ≤ Module.finrank K M := by
      by_contra hcon
      have hzero : Module.finrank K M = 0 := by omega
      have := (Module.finrank_zero_iff (R := K) (M := M)).mp hzero
      exact ha (Subsingleton.elim _ _)
    obtain ⟨m, hm⟩ : ∃ m, Module.finrank K M = m + 1 := ⟨Module.finrank K M - 1, by omega⟩
    have hpascal : (m + 1).choose (p + 1) = m.choose p + m.choose (p + 1) :=
      Nat.choose_succ_succ m p
    have hker : Module.finrank K (LinearMap.ker (exteriorPower.map (p + 1) π)) =
        (Module.finrank K M - 1).choose p := by
      rw [hm] at hrn ⊢
      simp only [Nat.add_sub_cancel] at hrn ⊢
      omega
    calc Module.finrank K (LinearMap.range (wedgeLeft K M p a))
        ≤ Module.finrank K (LinearMap.ker (exteriorPower.map (p + 1) π)) :=
          Submodule.finrank_mono hle
      _ = (Module.finrank K M - 1).choose p := hker

end WedgeFinrank

/-! ### Contracting the `Y` leg -/

section Slice

variable {K : Type u} [CommRing K] {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- The multilinear form behind `sliceY`: `(x, y, z) ↦ β y • (x ⊗ z)`. -/
def sliceYMultilinear (β : Module.Dual K (V .Y)) :
    MultilinearMap K V (TensorProduct K (V .X) (V .Z)) :=
  MultilinearMap.mk'
    (fun x ↦ β (x .Y) • ((x .X) ⊗ₜ[K] (x .Z)))
    (fun x i a b ↦ by
      cases i <;>
        simp [add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add, smul_add])
    (fun x i a b ↦ by
      cases i <;>
        simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm])

/-- Contract the `Y` leg of a three-legged tensor against a dual vector `β`, leaving an element
of `V_X ⊗ V_Z`.  This is the "one-leg-only" partial flattening used to build the Koszul map. -/
noncomputable def sliceY (β : Module.Dual K (V .Y)) :
    Tensor3 K V →ₗ[K] TensorProduct K (V .X) (V .Z) :=
  PiTensorProduct.lift (sliceYMultilinear β)

/-- The `Y` contraction of a pure tensor `x ⊗ y ⊗ z` is `β y • (x ⊗ z)`. -/
@[simp] theorem sliceY_pure (β : Module.Dual K (V .Y)) (x : ∀ c, V c) :
    sliceY β (pure (K := K) x) = β (x .Y) • ((x .X) ⊗ₜ[K] (x .Z)) := by
  simp [sliceY, sliceYMultilinear]

/-- `sliceY` packaged as a linear map in the dual vector, so that the Koszul flattening can be
assembled from bilinear data. -/
noncomputable def sliceYL :
    Module.Dual K (V .Y) →ₗ[K] (Tensor3 K V →ₗ[K] TensorProduct K (V .X) (V .Z)) where
  toFun := sliceY
  map_add' β₁ β₂ := by
    have h : sliceYMultilinear (V := V) (β₁ + β₂) =
        sliceYMultilinear (V := V) β₁ + sliceYMultilinear β₂ := by
      refine MultilinearMap.ext fun x ↦ ?_
      simp [sliceYMultilinear, add_smul]
    simp only [sliceY, h, map_add]
  map_smul' c β := by
    have h : sliceYMultilinear (V := V) (c • β) = c • sliceYMultilinear (V := V) β := by
      refine MultilinearMap.ext fun x ↦ ?_
      simp [sliceYMultilinear, mul_smul]
    simp only [sliceY, h, map_smul, RingHom.id_apply]

/-- `sliceYL` evaluates to `sliceY`. -/
@[simp] theorem sliceYL_apply (β : Module.Dual K (V .Y)) : sliceYL (V := V) β = sliceY β := rfl

end Slice

/-! ### The Koszul flattening -/

section Flattening

variable {K : Type u} [CommRing K] {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Wedging the `V_X` factor of `V_X ⊗ V_Z` on the left into a fixed `ω : ⋀^p V_X`, linearly
in `ω`. -/
noncomputable def wedgeRTensor (p : ℕ) :
    (⋀[K]^p (V .X)) →ₗ[K] (TensorProduct K (V .X) (V .Z) →ₗ[K]
      TensorProduct K (⋀[K]^(p + 1) (V .X)) (V .Z)) where
  toFun ω := LinearMap.rTensor (V .Z) ((wedgeLeft K (V .X) p).flip ω)
  map_add' ω₁ ω₂ := by
    refine TensorProduct.ext' fun x z ↦ ?_
    simp [LinearMap.rTensor_tmul]
  map_smul' c ω := by
    refine TensorProduct.ext' fun x z ↦ ?_
    simp [LinearMap.rTensor_tmul, TensorProduct.smul_tmul']

/-- Evaluation of `wedgeRTensor` on an elementary tensor. -/
@[simp] theorem wedgeRTensor_tmul (p : ℕ) (ω : ⋀[K]^p (V .X)) (x : V .X) (z : V .Z) :
    wedgeRTensor (V := V) p ω (x ⊗ₜ[K] z) = (wedgeLeft K (V .X) p x ω) ⊗ₜ[K] z := by
  simp [wedgeRTensor, LinearMap.rTensor_tmul]

/-- The bilinear data `(ω, β) ↦ (T ↦ (X-leg of β-contraction of T) ∧ ω ⊗ Z-leg)` out of which
the Koszul flattening is assembled. -/
noncomputable def koszulBilin (p : ℕ) :
    (⋀[K]^p (V .X)) →ₗ[K] Module.Dual K (V .Y) →ₗ[K]
      (Tensor3 K V →ₗ[K] TensorProduct K (⋀[K]^(p + 1) (V .X)) (V .Z)) :=
  ((LinearMap.llcomp K (Tensor3 K V) (TensorProduct K (V .X) (V .Z))
      (TensorProduct K (⋀[K]^(p + 1) (V .X)) (V .Z))) ∘ₗ (wedgeRTensor (V := V) p)).compl₂
    sliceYL

/-- The **`p`-th Koszul flattening** of a three-legged tensor: the linear map

```text
  Φ_T^p : (⋀^p V_X) ⊗ V_Y*  →  (⋀^{p+1} V_X) ⊗ V_Z,
     ω ⊗ β  ↦  (X-leg of the β-contraction of T) ∧ ω,  tensored with the Z-leg,
```

itself linear in `T`.  For `p = 0` this is the classical `X`-flattening of `T` (up to the
canonical identification `⋀^0 V_X ≅ K` and `⋀^1 V_X ≅ V_X`); for `p ≥ 1` it is a strictly
stronger invariant.

The `p = 0` identification is proved as `Tensor.contractX_eq_sliceY`, which relates `sliceY` to
`contractX` of `Tensor/Concise.lean`.  It cannot live here — this module deliberately does not
import `Tensor/Concise` — so it is homed in
`MatrixMultiplication/KoszulBorderRank.lean`, the first file that imports both. -/
noncomputable def koszulFlattening (p : ℕ) :
    Tensor3 K V →ₗ[K]
      (TensorProduct K (⋀[K]^p (V .X)) (Module.Dual K (V .Y)) →ₗ[K]
        TensorProduct K (⋀[K]^(p + 1) (V .X)) (V .Z)) :=
  (TensorProduct.lift (koszulBilin (V := V) p)).flip

/-- Evaluating the Koszul flattening on an elementary argument `ω ⊗ β`: contract `T` in the `Y`
leg against `β`, then wedge the resulting `V_X` factor into `ω`. -/
@[simp] theorem koszulFlattening_tmul (p : ℕ) (T : Tensor3 K V)
    (ω : ⋀[K]^p (V .X)) (β : Module.Dual K (V .Y)) :
    koszulFlattening (V := V) p T (ω ⊗ₜ[K] β) =
      wedgeRTensor (V := V) p ω (sliceY β T) := by
  simp [koszulFlattening, koszulBilin]

/-- The Koszul flattening of a pure tensor `x ⊗ y ⊗ z`, evaluated on `ω ⊗ β`, is
`β y • ((x ∧ ω) ⊗ z)`. -/
theorem koszulFlattening_pure_tmul (p : ℕ) (x : ∀ c, V c)
    (ω : ⋀[K]^p (V .X)) (β : Module.Dual K (V .Y)) :
    koszulFlattening (V := V) p (pure (K := K) x) (ω ⊗ₜ[K] β) =
      β (x .Y) • ((wedgeLeft K (V .X) p (x .X) ω) ⊗ₜ[K] (x .Z)) := by
  rw [koszulFlattening_tmul, sliceY_pure, map_smul, wedgeRTensor_tmul]

end Flattening

/-! ### The rank lower bound -/

section RankBound

variable {K : Type u} [Field K] {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

variable [∀ i, FiniteDimensional K (V i)]

/-- The target space of the `p`-th Koszul flattening is finite dimensional.  Registered as a
local instance so that the dimension estimates below do not repeat the search. -/
private instance koszulTargetFiniteDimensional (p : ℕ) :
    FiniteDimensional K (TensorProduct K (⋀[K]^(p + 1) (V .X)) (V .Z)) :=
  Module.Finite.tensorProduct K (⋀[K]^(p + 1) (V .X)) (V .Z)

/-- **Rank-one estimate.**  The `p`-th Koszul flattening of a pure tensor has rank at most
`binom (dim V_X - 1) p`.

Proof sketch: on the elementary argument `ω ⊗ β` the value is `β y • ((x ∧ ω) ⊗ z)`, which lies
in the image of `⋀^{p+1} V_X → ⋀^{p+1} V_X ⊗ V_Z`, `u ↦ u ⊗ z`, applied to the image of
`x ∧ · : ⋀^p V_X → ⋀^{p+1} V_X`.  Elementary tensors span, so the whole range lies in that
image, whose dimension is bounded by `finrank_range_wedgeLeft_le`. -/
theorem finrank_range_koszulFlattening_pure_le (p : ℕ) (x : ∀ c, V c) :
    Module.finrank K (LinearMap.range (koszulFlattening (V := V) p (pure (K := K) x))) ≤
      (Module.finrank K (V .X) - 1).choose p := by
  classical
  set w : (⋀[K]^p (V .X)) →ₗ[K] (⋀[K]^(p + 1) (V .X)) := wedgeLeft K (V .X) p (x .X) with hw
  set g : (⋀[K]^(p + 1) (V .X)) →ₗ[K] TensorProduct K (⋀[K]^(p + 1) (V .X)) (V .Z) :=
    (TensorProduct.mk K (⋀[K]^(p + 1) (V .X)) (V .Z)).flip (x .Z) with hg
  have hle : LinearMap.range (koszulFlattening (V := V) p (pure (K := K) x)) ≤
      LinearMap.range (g ∘ₗ w) := by
    rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨t, ⟨ω, β, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, koszulFlattening_pure_tmul]
    refine Submodule.smul_mem _ _ ⟨ω, ?_⟩
    rw [LinearMap.comp_apply, hg]
    rfl
  calc Module.finrank K (LinearMap.range (koszulFlattening (V := V) p (pure (K := K) x)))
      ≤ Module.finrank K (LinearMap.range (g ∘ₗ w)) := Submodule.finrank_mono hle
    _ = Module.finrank K (Submodule.map g (LinearMap.range w)) := by rw [LinearMap.range_comp]
    _ ≤ Module.finrank K (LinearMap.range w) := Submodule.finrank_map_le g _
    _ ≤ (Module.finrank K (V .X) - 1).choose p := finrank_range_wedgeLeft_le p (x .X)

/-- **The Koszul flattening rank bound**, in the form clients use: if `T` has a rank-`r`
certificate, then no more than `r * binom (dim V_X - 1) p` values of the `p`-th Koszul
flattening of `T` can be linearly independent.

Equivalently: `rank (Φ_T^p) ≤ r · binom (dim V_X - 1) p`, phrased through linear independence
rather than through `finrank (range ·)` because the latter forces dimension lemmas onto the
tensor-product target, where Lean's `AddCommMonoid`/`AddCommGroup` instance diamond for
`⋀^{p+1} V_X ⊗ V_Z` makes elaboration prohibitively expensive.

Proof sketch: let `T = ∑_{j<m} x_j` with `m ≤ r`.  Every value
`Φ_T^p (ω ⊗ β) = ∑_j β(y_j) • ((x_j ∧ ω) ⊗ z_j)` lies in the image of the single linear map

```text
  Ψ : ∏_j W_j → ⋀^{p+1} V_X ⊗ V_Z,   Ψ v = ∑_j (v j) ⊗ z_j,
```

where `W_j` is a coordinate copy of the image `x_j ∧ ⋀^p V_X`, of dimension at most
`binom (dim V_X - 1) p` by `finrank_range_wedgeLeft_le`.  Elementary tensors span the source of
`Φ_T^p`, so every value of `Φ_T^p` is `Ψ v` for some `v`; choosing such preimages turns a
linearly independent family of values into a linearly independent family in `∏_j W_j`, whose
size is at most `∑_j dim W_j ≤ m · binom (dim V_X - 1) p`.

The `W_j` are taken inside a coordinate space `ChooseBasisIndex → K` rather than inside
`⋀^{p+1} V_X` itself: submodules of the submodule-coercion `⋀^{p+1} V_X` do not get a usable
`Module.Free` instance, which the product-dimension formula needs. -/
theorem RankLE.card_le_of_linearIndependent_koszulFlattening
    {r : ℕ} {T : Tensor3 K V} (hT : RankLE r T) (p : ℕ)
    {ι : Type*} [Fintype ι]
    (u : ι → TensorProduct K (⋀[K]^p (V .X)) (Module.Dual K (V .Y)))
    (hu : LinearIndependent K fun i ↦ koszulFlattening (V := V) p T (u i)) :
    Fintype.card ι ≤ r * (Module.finrank K (V .X) - 1).choose p := by
  classical
  obtain ⟨terms, hlen, rfl⟩ := hT
  set x : Fin terms.length → (∀ i, V i) := fun j ↦ terms.get j with hxdef
  -- a coordinate model of `⋀^{p+1} V_X`
  set Ex : (⋀[K]^(p + 1) (V .X)) ≃ₗ[K]
      (Module.Free.ChooseBasisIndex K (⋀[K]^(p + 1) (V .X)) → K) :=
    (Module.Free.chooseBasis K (⋀[K]^(p + 1) (V .X))).equivFun with hExdef
  set EL : (⋀[K]^(p + 1) (V .X)) →ₗ[K]
      (Module.Free.ChooseBasisIndex K (⋀[K]^(p + 1) (V .X)) → K) :=
    Ex.toLinearMap with hELdef
  set ER : (Module.Free.ChooseBasisIndex K (⋀[K]^(p + 1) (V .X)) → K) →ₗ[K]
      (⋀[K]^(p + 1) (V .X)) := Ex.symm.toLinearMap with hERdef
  have hERL : ∀ y : (⋀[K]^(p + 1) (V .X)), ER (EL y) = y := by
    intro y
    rw [hERdef, hELdef]
    exact Ex.symm_apply_apply y
  set W : Fin terms.length →
      Submodule K (Module.Free.ChooseBasisIndex K (⋀[K]^(p + 1) (V .X)) → K) :=
    fun j ↦ Submodule.map EL (LinearMap.range (wedgeLeft K (V .X) p ((x j) .X))) with hWdef
  have hWj : ∀ j : Fin terms.length, W j =
      Submodule.map EL (LinearMap.range (wedgeLeft K (V .X) p ((x j) .X))) := by
    intro j
    simp [hWdef]
  set Ψ : (∀ j : Fin terms.length, (W j)) →ₗ[K]
      TensorProduct K (⋀[K]^(p + 1) (V .X)) (V .Z) :=
    ∑ j : Fin terms.length,
      ((TensorProduct.mk K (⋀[K]^(p + 1) (V .X)) (V .Z)).flip ((x j) .Z)) ∘ₗ
        (ER ∘ₗ ((W j).subtype ∘ₗ (LinearMap.proj j))) with hΨdef
  have hΨ_apply : ∀ v : (∀ j : Fin terms.length, (W j)),
      Ψ v = ∑ j : Fin terms.length, ((ER (v j : _)) ⊗ₜ[K] ((x j) .Z)) := by
    intro v
    rw [hΨdef, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp
  have hsub : LinearMap.range
      (koszulFlattening (V := V) p ((terms.map (pure (K := K))).sum)) ≤ LinearMap.range Ψ := by
    rw [LinearMap.range_eq_map, ← TensorProduct.span_tmul_eq_top, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨t, ⟨ω, β, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe]
    refine ⟨fun j ↦ ⟨EL (β ((x j) .Y) • (wedgeLeft K (V .X) p ((x j) .X) ω)), ?_⟩, ?_⟩
    · rw [hWj j]
      exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ ⟨ω, rfl⟩)
    · rw [hΨ_apply, list_map_sum_eq_fin_sum (pure (K := K)) terms, map_sum,
        LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [koszulFlattening_pure_tmul, hERL]
      exact TensorProduct.smul_tmul' _ _ _
  -- choose preimages under `Ψ` of the values of the Koszul flattening
  have hpre : ∀ q, ∃ v : (∀ j : Fin terms.length, (W j)),
      Ψ v = koszulFlattening (V := V) p ((terms.map (pure (K := K))).sum) q :=
    fun q ↦ hsub (LinearMap.mem_range_self _ q)
  choose v hv using hpre
  have hcomp : LinearIndependent K fun i ↦ Ψ (v (u i)) := by
    simpa only [hv] using hu
  have hvind : LinearIndependent K fun i ↦ v (u i) :=
    LinearIndependent.of_comp Ψ hcomp
  refine hvind.fintype_card_le_finrank.trans ?_
  have hpi : Module.finrank K (∀ j : Fin terms.length, (W j)) =
      ∑ j : Fin terms.length, Module.finrank K (W j) := Module.finrank_pi_fintype K
  have hbound : ∑ j : Fin terms.length, Module.finrank K (W j) ≤
      terms.length * (Module.finrank K (V .X) - 1).choose p := by
    calc ∑ j : Fin terms.length, Module.finrank K (W j)
        ≤ ∑ _j : Fin terms.length, (Module.finrank K (V .X) - 1).choose p := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [hWj j]
          exact (Submodule.finrank_map_le EL
            (LinearMap.range (wedgeLeft K (V .X) p ((x j) .X)))).trans
            (finrank_range_wedgeLeft_le p ((x j) .X))
      _ = terms.length * (Module.finrank K (V .X) - 1).choose p := by
          simp [Finset.sum_const, mul_comm]
  calc Module.finrank K (∀ j : Fin terms.length, (W j))
      = ∑ j : Fin terms.length, Module.finrank K (W j) := hpi
    _ ≤ terms.length * (Module.finrank K (V .X) - 1).choose p := hbound
    _ ≤ r * (Module.finrank K (V .X) - 1).choose p := Nat.mul_le_mul hlen (le_refl _)

/-- Client-facing contrapositive: `s` linearly independent values of the `p`-th Koszul
flattening of `T` with `r * binom (dim V_X - 1) p < s` force `rank T > r`. -/
theorem lt_rank_of_linearIndependent_koszulFlattening {r p : ℕ} {T : Tensor3 K V}
    {ι : Type*} [Fintype ι]
    (u : ι → TensorProduct K (⋀[K]^p (V .X)) (Module.Dual K (V .Y)))
    (hu : LinearIndependent K fun i ↦ koszulFlattening (V := V) p T (u i))
    (hcard : r * (Module.finrank K (V .X) - 1).choose p < Fintype.card ι) :
    r < rank T := by
  by_contra hcon
  have hle : rank T ≤ r := Nat.le_of_not_lt hcon
  have hbound := (rank_spec T).card_le_of_linearIndependent_koszulFlattening p u hu
  have hmono : rank T * (Module.finrank K (V .X) - 1).choose p ≤
      r * (Module.finrank K (V .X) - 1).choose p := Nat.mul_le_mul hle (le_refl _)
  omega

end RankBound

end AlgebraicComplexity.Tensor
