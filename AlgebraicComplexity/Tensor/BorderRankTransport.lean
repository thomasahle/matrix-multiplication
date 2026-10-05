/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Polynomial

/-!
# Transporting border-rank certificates along transpositions and restrictions

`Tensor/BorderRank.lean` transports a constructive border-rank certificate along the *cyclic*
leg rotation only, and `Tensor/Polynomial.lean` proves the corresponding naturality of
`polynomialPure` only for `cycle`.  The cyclic rotations form the alternating subgroup of the
three leg permutations, so a certificate for `⟨m,n,p⟩` can be rotated to `⟨p,m,n⟩` and `⟨n,p,m⟩`
but never *transposed* to `⟨n,m,p⟩`.  Clients that reverse two legs — Coppersmith's 1982
rectangular construction does, and every rectangular pipeline that has to normalize which of the
three dimensions is the small one does — need the missing odd generator.

This module supplies it, together with the two degree-aware transport laws that
`Tensor/Polynomial.lean` and `Tensor/Degeneration.lean` state for `BorderRankLE` but not for
`BorderRankLEAt`.

## Principal results

* `polynomialPure_permute_xzy`: naturality of the convolutional pure tensor under the leg
  transposition `xzy`, the exact analogue of `polynomialPure_permute_cycle`.  Together with the
  cyclic case this covers a generating set of the symmetric group on the three legs;
* `BorderRankLEAt.permute_xzy`, `BorderRankLE.permute_xzy`: transposing the `Y` and `Z` legs
  preserves every constructive border-rank certificate, with the leading degree unchanged;
* `BorderRankLEAt.permute_cycle`: the degree-aware form of `BorderRankLE.permute_cycle`;
* `BorderRankLEAt.of_restricts` and `BorderRankLEAt.isomorphic`: the degree-aware forms of
  `BorderRankLE.of_restricts` and `BorderRankLE.isomorphic`.  Restriction acts by fixed linear
  maps, so it changes neither the number of terms nor the leading degree; this is what lets a
  degree-aware certificate be pushed through a retyping isomorphism without losing the degree
  bookkeeping that polynomial interpolation depends on.

## Layer placement

Layer 1 (tensor algebra), a leaf immediately downstream of `Tensor/Polynomial.lean`, which is
where `BorderRankLE` and `BorderRankLEAt` are defined.  The statements belong logically next to
their cyclic siblings in `Tensor/Polynomial.lean`, `Tensor/Degeneration.lean` and
`Tensor/BorderRank.lean`; they are collected in a separate leaf so that adding them does not
force a rebuild of every module in the tree.  Keeping the import at `Tensor/Polynomial.lean`
rather than `Tensor/BorderRank.lean` also keeps elaboration of the dependent leg-reindexing
statements comfortably inside the project's 768 MB budget.
-/

namespace AlgebraicComplexity.Tensor

open PolynomialVector

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-! ## Naturality of `polynomialPure` under the leg transposition -/

/-- The monomial case of transposition naturality for polynomial pure tensors: the total degree
`dx + dy + dz` is invariant under transposing two of the three legs, and `Tensor.permute_pure`
transposes the pure tensor of coefficients. -/
private theorem polynomialPure_permute_xzy_monomial (dx dy dz : ℕ)
    (vx : V .X) (vy : V .Y) (vz : V .Z) :
    PolynomialVector.mapLinear
        (Tensor.permute (K := K) (V := V) xzy).toLinearMap
        (polynomialPure (K := K) (ofLegs
          (PolynomialVector.monomial dx vx)
          (PolynomialVector.monomial dy vy)
          (PolynomialVector.monomial dz vz))) =
      polynomialPure (K := K) (V := fun i ↦ V (xzy.symm i)) (ofLegs
        (PolynomialVector.monomial dx vx)
        (PolynomialVector.monomial dz vz)
        (PolynomialVector.monomial dy vy)) := by
  have hfam :
      (fun i ↦ ofLegs vx vy vz (xzy.symm i)) =
        ofLegs (V := fun i ↦ V (xzy.symm i)) vx vz vy := by
    funext c
    cases c <;> rfl
  rw [polynomialPure_monomial, PolynomialVector.mapLinear_monomial,
    polynomialPure_monomial (K := K) (V := fun i ↦ V (xzy.symm i))
      dx dz dy vx vz vy,
    show dx + dz + dy = dx + dy + dz from by ring,
    LinearEquiv.coe_coe, Tensor.permute_pure, hfam]

/-- Transposition naturality with the two outer legs pinned to monomials.  Both sides are
additive in the remaining polynomial vector, so `Finsupp.induction_linear` reduces to
`polynomialPure_permute_xzy_monomial`. -/
private theorem polynomialPure_permute_xzy_monomialXY (dx dy : ℕ)
    (vx : V .X) (vy : V .Y) (xZ : PolynomialVector (V .Z)) :
    PolynomialVector.mapLinear
        (Tensor.permute (K := K) (V := V) xzy).toLinearMap
        (polynomialPure (K := K) (ofLegs
          (PolynomialVector.monomial dx vx)
          (PolynomialVector.monomial dy vy) xZ)) =
      polynomialPure (K := K) (V := fun i ↦ V (xzy.symm i)) (ofLegs
        (PolynomialVector.monomial dx vx) xZ
        (PolynomialVector.monomial dy vy)) := by
  classical
  induction xZ using Finsupp.induction_linear with
  | zero =>
      simp only [polynomialPure_zero_Z, map_zero]
      exact (polynomialPure_zero_Y (K := K) (V := fun i ↦ V (xzy.symm i))
        (PolynomialVector.monomial dx vx) (PolynomialVector.monomial dy vy)).symm
  | add a b ha hb =>
      simp only [polynomialPure_add_Z, map_add, ha, hb]
      exact (polynomialPure_add_Y (K := K) (V := fun i ↦ V (xzy.symm i))
        (PolynomialVector.monomial dx vx) a b (PolynomialVector.monomial dy vy)).symm
  | single dz vz =>
      exact polynomialPure_permute_xzy_monomial (K := K) dx dy dz vx vy vz

/-- Transposition naturality with the `X` leg pinned to a monomial. -/
private theorem polynomialPure_permute_xzy_monomialX (dx : ℕ) (vx : V .X)
    (xY : PolynomialVector (V .Y)) (xZ : PolynomialVector (V .Z)) :
    PolynomialVector.mapLinear
        (Tensor.permute (K := K) (V := V) xzy).toLinearMap
        (polynomialPure (K := K) (ofLegs
          (PolynomialVector.monomial dx vx) xY xZ)) =
      polynomialPure (K := K) (V := fun i ↦ V (xzy.symm i)) (ofLegs
        (PolynomialVector.monomial dx vx) xZ xY) := by
  classical
  induction xY using Finsupp.induction_linear with
  | zero =>
      simp only [polynomialPure_zero_Y, map_zero]
      exact (polynomialPure_zero_Z (K := K) (V := fun i ↦ V (xzy.symm i))
        (PolynomialVector.monomial dx vx) xZ).symm
  | add a b ha hb =>
      simp only [polynomialPure_add_Y, map_add, ha, hb]
      exact (polynomialPure_add_Z (K := K) (V := fun i ↦ V (xzy.symm i))
        (PolynomialVector.monomial dx vx) xZ a b).symm
  | single dy vy =>
      exact polynomialPure_permute_xzy_monomialXY (K := K) dx dy vx vy xZ

/-- Explicit three-leg form of transposition naturality for polynomial pure tensors: permuting the
legs of the source path `polynomialPure (ofLegs xX xY xZ)` by the transposition `Y ↔ Z` gives the
polynomial pure path of the transposed triple `(xX, xZ, xY)`.

Proof sketch: the same triple `Finsupp.induction_linear` as
`polynomialPure_permute_cycle_ofLegs`, split into three separate lemmas so that no single
elaboration carries all three dependent leg reindexings at once. -/
private theorem polynomialPure_permute_xzy_ofLegs
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) :
    PolynomialVector.mapLinear
        (Tensor.permute (K := K) (V := V) xzy).toLinearMap
        (polynomialPure (K := K) (ofLegs xX xY xZ)) =
      polynomialPure (K := K) (V := fun i ↦ V (xzy.symm i)) (ofLegs xX xZ xY) := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero =>
      simp only [polynomialPure_zero_X, map_zero]
      exact (polynomialPure_zero_X (K := K) (V := fun i ↦ V (xzy.symm i)) xZ xY).symm
  | add a b ha hb =>
      simp only [polynomialPure_add_X, map_add, ha, hb]
      exact (polynomialPure_add_X (K := K) (V := fun i ↦ V (xzy.symm i)) a b xZ xY).symm
  | single dx vx =>
      exact polynomialPure_permute_xzy_monomialX (K := K) dx vx xY xZ

/-- The leg transposition `Y ↔ Z` commutes with polynomial pure tensors, coefficient by
coefficient: permuting the legs of the polynomial pure path of `x` by `xzy` gives the polynomial
pure path of the reindexed family `fun c ↦ x (xzy.symm c)`.

This is the odd-permutation companion of `polynomialPure_permute_cycle`; since `cycle` and `xzy`
generate all six leg permutations, the two together transport a polynomial certificate along an
arbitrary reindexing of the three legs. -/
theorem polynomialPure_permute_xzy (x : ∀ c, PolynomialVector (V c)) :
    PolynomialVector.mapLinear
        (Tensor.permute (K := K) (V := V) xzy).toLinearMap
        (polynomialPure (K := K) x) =
      polynomialPure (K := K) (V := fun i ↦ V (xzy.symm i))
        (fun c ↦ x (xzy.symm c)) := by
  rw [← ofLegs_eta x]
  convert polynomialPure_permute_xzy_ofLegs (K := K) (V := V)
    (x .X) (x .Y) (x .Z) using 1
  congr 1
  funext c
  cases c <;> rfl

/-! ## Degree-aware transport laws -/

namespace BorderRankLEAt

/-- Transposing the `Y` and `Z` tensor legs preserves every degree-aware border-rank certificate:
a size-`r`, degree-`d` certificate for `T` gives one for `Tensor.permute xzy T`, with the same
size and the same leading degree.

Proof sketch: apply the linear equivalence `Tensor.permute xzy` coefficientwise to the
certificate path.  That preserves the leading degree and carries the leading coefficient `T` to
`Tensor.permute xzy T`, and `polynomialPure_permute_xzy` identifies the transported path with the
polynomial pure path of the termwise transposed list, which has the same length. -/
theorem permute_xzy {r d : ℕ} {T : Tensor3 K V} (h : BorderRankLEAt r d T) :
    BorderRankLEAt r d (Tensor.permute xzy T) := by
  rcases h with ⟨terms, hlen, hlead⟩
  refine ⟨terms.map fun x c ↦ x (xzy.symm c), by simpa using hlen, ?_⟩
  have hmapped := hlead.mapLinear (Tensor.permute (K := K) (V := V) xzy).toLinearMap
  have hpath :
      PolynomialVector.mapLinear (Tensor.permute (K := K) (V := V) xzy).toLinearMap
          (terms.map (polynomialPure (K := K))).sum =
        ((terms.map fun x c ↦ x (xzy.symm c)).map (polynomialPure (K := K))).sum := by
    rw [map_list_sum]
    simp [Function.comp_def, polynomialPure_permute_xzy]
  rw [← hpath]
  exact hmapped

/-- Cyclically reindexing the three tensor legs preserves every degree-aware border-rank
certificate.  This is the degree-retaining refinement of `BorderRankLE.permute_cycle`, proved the
same way from `polynomialPure_permute_cycle`. -/
theorem permute_cycle {r d : ℕ} {T : Tensor3 K V} (h : BorderRankLEAt r d T) :
    BorderRankLEAt r d (Tensor.permute cycle T) := by
  rcases h with ⟨terms, hlen, hlead⟩
  refine ⟨terms.map fun x c ↦ x (cycle.symm c), by simpa using hlen, ?_⟩
  have hmapped := hlead.mapLinear (Tensor.permute (K := K) (V := V) cycle).toLinearMap
  have hpath :
      PolynomialVector.mapLinear (Tensor.permute (K := K) (V := V) cycle).toLinearMap
          (terms.map (polynomialPure (K := K))).sum =
        ((terms.map fun x c ↦ x (cycle.symm c)).map (polynomialPure (K := K))).sum := by
    rw [map_list_sum]
    simp [Function.comp_def, polynomialPure_permute_cycle]
  rw [← hpath]
  exact hmapped

/-- Degree-aware border-rank certificates transfer along exact restriction: if legwise linear
maps carry the source `T` to the target `S`, a size-`r`, degree-`d` certificate for `T` gives one
for `S`.  Both the size and the leading degree are unchanged, because restriction acts by fixed
(degree-zero) linear maps.  This is the degree-retaining form of `BorderRankLE.of_restricts`. -/
theorem of_restricts {r d : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : BorderRankLEAt r d T) (hTS : Restricts T S) : BorderRankLEAt r d S := by
  rcases hTS with ⟨f, rfl⟩
  exact h.map f

/-- Degree-aware border-rank certificates are invariant under legwise linear isomorphism, with
both the size and the leading degree preserved. -/
theorem isomorphic {r d : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hTS : Isomorphic T S) : BorderRankLEAt r d T ↔ BorderRankLEAt r d S :=
  ⟨fun hT ↦ hT.of_restricts hTS.restricts, fun hS ↦ hS.of_restricts hTS.symm.restricts⟩

end BorderRankLEAt

namespace BorderRankLE

/-- Transposing the `Y` and `Z` tensor legs preserves every constructive border-rank certificate.
This is the odd-permutation companion of `BorderRankLE.permute_cycle`, obtained by forgetting the
leading degree in `BorderRankLEAt.permute_xzy`. -/
theorem permute_xzy {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    BorderRankLE r (Tensor.permute xzy T) := by
  obtain ⟨d, hd⟩ := h.exists_at
  exact hd.permute_xzy.toBorderRankLE

end BorderRankLE

end AlgebraicComplexity.Tensor
