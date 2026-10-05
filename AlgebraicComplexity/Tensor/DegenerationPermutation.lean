/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Degeneration

/-!
# Leg permutations act on polynomial degenerations

Layer 1 (`AlgebraicComplexity/Tensor/`).  `Tensor/Restriction.lean` already proves that an exact
restriction survives an arbitrary permutation of the three tensor legs
(`Restricts.permute`).  This module supplies the corresponding statement for the constructive
one-parameter degeneration of `Tensor/Degeneration.lean`:

`T ⊵ S  ⟹  T^e ⊵ S^e` for every `e : Orientation`,

with the displayed leading degree unchanged.

## Why this is not immediate

`polynomialTransform A T` is defined as a *nested* `Finsupp.sum` over the coefficient degrees of
the three leg families `A .X`, `A .Y`, `A .Z`, in that fixed leg order.  Permuting the legs
permutes the three sums, so the statement is not a rewriting of the definition.  The proof here
first rewrites the nested sum into the manifestly leg-symmetric form

`∑_{d ∈ piFinset (fun c ↦ (A c).support)} ε^{∑_c d c} · map (fun c ↦ A c (d c)) T`,

a single sum over leg-indexed degree functions, and then reindexes that sum along
`d ↦ d ∘ e.symm`.  Two facts make the reindexed summand match: the total degree `∑_c d c` is
invariant under precomposition with a permutation (`Equiv.sum_comp`), and
`PiTensorProduct.map_reindex` moves the leg permutation across a legwise map.

## Principal results

* `Tensor.polynomialTransform_eq_piFinset_sum` — the leg-symmetric form of
  `polynomialTransform`.
* `Tensor.polynomialTransform_permute` — the naturality equation
  `polynomialTransform (A ∘ e.symm) (T^e) = (polynomialTransform A T)^e`.
* `Tensor.PolynomialDegeneratesAt.permute` and `Tensor.PolynomialDegenerates.permute` — the
  degeneration relation is preserved by every leg permutation, at the same displayed degree.

## Non-goals

Nothing here is specific to matrix multiplication or to a named orientation; the three-orientation
and six-orientation value constructions that consume these lemmas live in layer 3.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-! ## Sums indexed by leg-indexed degree functions -/

/-- A sum over leg-indexed degree functions is the corresponding triple nested sum.

Proof sketch: the explicit bijection `d ↦ (d .X, d .Y, d .Z)` identifies
`Fintype.piFinset t` with `t .X ×ˢ t .Y ×ˢ t .Z`; its inverse is `ofLegs`. -/
theorem sum_piFinset_leg {M : Type*} [AddCommMonoid M] (t : Leg → Finset ℕ)
    (f : (Leg → ℕ) → M) :
    ∑ d ∈ Fintype.piFinset t, f d =
      ∑ a ∈ t .X, ∑ b ∈ t .Y, ∑ c ∈ t .Z, f (ofLegs a b c) := by
  classical
  have hprod : ∑ a ∈ t .X, ∑ b ∈ t .Y, ∑ c ∈ t .Z, f (ofLegs a b c) =
      ∑ x ∈ (t .X) ×ˢ ((t .Y) ×ˢ (t .Z)), f (ofLegs x.1 x.2.1 x.2.2) := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Finset.sum_product]
  rw [hprod]
  refine Finset.sum_nbij' (i := fun d ↦ (d .X, d .Y, d .Z))
    (j := fun x ↦ ofLegs x.1 x.2.1 x.2.2) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Fintype.mem_piFinset] at hd
    simp only [Finset.mem_product]
    exact ⟨hd .X, hd .Y, hd .Z⟩
  · intro x hx
    simp only [Finset.mem_product] at hx
    rw [Fintype.mem_piFinset]
    intro c
    cases c
    · exact hx.1
    · exact hx.2.1
    · exact hx.2.2
  · intro d _
    funext c
    cases c <;> rfl
  · intro x _
    rfl
  · intro d _
    congr 1
    funext c
    cases c <;> rfl

/-! ## The leg-symmetric form of `polynomialTransform` -/

/-- **`polynomialTransform` written as one sum over leg-indexed degree functions.**

`polynomialTransform A T` is defined as three nested `Finsupp.sum`s, one per leg, in the fixed
order `X`, `Y`, `Z`.  This reformulation replaces them by a single sum over the functions
`d : Leg → ℕ` whose value at each leg is a supported degree of that leg's coefficient family; the
monomial degree is the total `∑_c d c` and the transformed tensor is the legwise map
`fun c ↦ A c (d c)`.  In this form no leg is distinguished, which is what makes the leg
permutation lemma below a reindexing rather than a case analysis. -/
theorem polynomialTransform_eq_piFinset_sum
    (A : ∀ c, PolynomialLinearMap K (V c) (W c)) (T : Tensor3 K V) :
    polynomialTransform A T =
      ∑ d ∈ Fintype.piFinset (fun c ↦ (A c).support),
        PolynomialVector.monomial (∑ c, d c) (map (fun c ↦ A c (d c)) T) := by
  classical
  rw [sum_piFinset_leg]
  show (A .X).sum (fun dx _ ↦ (A .Y).sum fun dy _ ↦ (A .Z).sum fun dz fz ↦
      PolynomialVector.monomial (dx + dy + dz) (map (ofLegs _ _ fz) T)) = _
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun dx _ ↦ Finset.sum_congr rfl fun dy _ ↦
    Finset.sum_congr rfl fun dz _ ↦ ?_
  have hdeg : ∑ c : Leg, (ofLegs dx dy dz : Leg → ℕ) c = dx + dy + dz := sum_leg _
  have hfam : (fun c ↦ A c ((ofLegs dx dy dz : Leg → ℕ) c)) =
      ofLegs (A .X dx) (A .Y dy) (A .Z dz) := by
    funext c
    cases c <;> rfl
  rw [hdeg, hfam]

/-! ## Naturality under leg permutations -/

/-- **Permuting the legs commutes with polynomial transformation.**  Transforming the permuted
tensor `T^e` by the permuted coefficient family `A ∘ e.symm` gives the permutation of the
transformed polynomial path of `T`.

Proof sketch: rewrite both sides in the leg-symmetric form above and reindex the left sum along
`d ↦ d ∘ e.symm`.  Membership in the two `piFinset`s corresponds because
`e.symm` is a bijection of legs; the monomial degrees agree by `Equiv.sum_comp`; and the two
transformed tensors agree by `PiTensorProduct.map_reindex`. -/
theorem polynomialTransform_permute (e : Orientation)
    (A : ∀ c, PolynomialLinearMap K (V c) (W c)) (T : Tensor3 K V) :
    polynomialTransform (fun c ↦ A (e.symm c)) (Tensor.permute e T) =
      PolynomialVector.mapLinear
        (Tensor.permute (K := K) (V := W) e).toLinearMap (polynomialTransform A T) := by
  classical
  rw [polynomialTransform_eq_piFinset_sum, polynomialTransform_eq_piFinset_sum, map_sum]
  refine (Finset.sum_nbij' (i := fun d : Leg → ℕ ↦ fun c ↦ d (e.symm c))
    (j := fun d : Leg → ℕ ↦ fun c ↦ d (e c)) ?_ ?_ ?_ ?_ ?_).symm
  · intro d hd
    rw [Fintype.mem_piFinset] at hd ⊢
    exact fun c ↦ hd (e.symm c)
  · intro d hd
    rw [Fintype.mem_piFinset] at hd ⊢
    intro c
    have hc := hd (e c)
    rwa [Equiv.symm_apply_apply] at hc
  · intro d _
    funext c
    simp
  · intro d _
    funext c
    simp
  · intro d _
    have hdeg : ∑ c : Leg, d (e.symm c) = ∑ c : Leg, d c :=
      Equiv.sum_comp e.symm (fun c ↦ d c)
    have hmap : map (fun c ↦ A (e.symm c) (d (e.symm c))) (Tensor.permute e T) =
        Tensor.permute e (map (fun c ↦ A c (d c)) T) :=
      PiTensorProduct.map_reindex (fun c ↦ A c (d c)) e T
    rw [PolynomialVector.mapLinear_monomial]
    rw [hdeg, hmap]
    rfl

namespace PolynomialDegeneratesAt

/-- **A polynomial degeneration survives every permutation of the three tensor legs**, with the
displayed leading degree unchanged.  Source is `T`, target is `S`; the conclusion relates the
permuted source `T^e` to the permuted target `S^e`.

Proof sketch: transport the coefficient family `A` to `A ∘ e.symm`, use
`polynomialTransform_permute` to identify the transformed path with the permutation of the
original path, and apply `HasLeadingTerm.mapLinear` to the linear map `Tensor.permute e`. -/
theorem permute {d : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegeneratesAt d T S) (e : Orientation) :
    PolynomialDegeneratesAt d (Tensor.permute e T) (Tensor.permute e S) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨fun c ↦ A (e.symm c), ?_⟩
  rw [polynomialTransform_permute]
  exact hA.mapLinear (Tensor.permute (K := K) (V := W) e).toLinearMap

end PolynomialDegeneratesAt

namespace PolynomialDegenerates

/-- **A polynomial degeneration survives every permutation of the three tensor legs.**  The
degree-forgetting corollary of `PolynomialDegeneratesAt.permute`. -/
theorem permute {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegenerates T S) (e : Orientation) :
    PolynomialDegenerates (Tensor.permute e T) (Tensor.permute e S) := by
  obtain ⟨d, hd⟩ := h.exists_at
  exact (hd.permute e).toPolynomialDegenerates

end PolynomialDegenerates

end AlgebraicComplexity.Tensor
