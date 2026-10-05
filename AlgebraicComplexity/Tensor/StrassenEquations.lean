/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import AlgebraicComplexity.Tensor.BorderRank
import AlgebraicComplexity.Tensor.Coordinates
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Strassen's commutation equations for minimal border rank

Layer 1 (`AlgebraicComplexity/Tensor/`).  This file proves the *commutation equations* of
[Strassen1983] in the constructive certificate style used throughout the repository: a tensor whose
`Z`-slices are square of size `n` and whose border rank is at most `n` has *commuting normalized
slices*.  This is the library's first border-rank lower bound that is not a flattening
(conciseness, Koszul) bound: the contrapositive is what has content, since a single non-vanishing
commutator already forbids minimal border rank.

## The identity

Fix a coefficient table with `Z`-slices `M_z : Matrix ι ι K`, `n = |ι|`.  The single algebraic fact
behind everything is

```text
M_{z₁} · adj(M_{z₃}) · M_{z₂} = M_{z₂} · adj(M_{z₃}) · M_{z₁}      for all z₁, z₂, z₃,
```

where `adj` is the adjugate.  It is *division-free* and holds over any commutative ring, which is
exactly what makes the passage to the border painless.

For an exact decomposition into `n` pure tensors (`mul_adjugate_mul_comm_of_sliceEntries`) the
proof is one line of matrix algebra: writing the `n` terms as the columns of two square matrices
`A`, `B` gives `M_z = A · D_z · Bᵀ` with `D_z` diagonal, and

```text
M_{z₁} adj(M_{z₃}) M_{z₂}
  = A D_{z₁} (Bᵀ adj Bᵀ) adj(D_{z₃}) (adj A · A) D_{z₂} Bᵀ
  = (det B · det A) · A (D_{z₁} adj(D_{z₃}) D_{z₂}) Bᵀ,
```

which is symmetric in `z₁, z₂` because diagonal matrices commute.

For a *border* certificate (`zSliceMatrix_mul_adjugate_mul_comm`) the same identity is applied over
the polynomial ring `K[X]`: a border-rank-`n` certificate is literally an exact `n`-term
decomposition over `K[X]` whose slices `M̃_z` are divisible by `X^d`, with the quotient specializing
at `X = 0` to the slice `M_z` of the leading tensor.  Since the adjugate is homogeneous of degree
`n - 1`, the common factor `X^{d(n+1)}` cancels — multiplication by `X^m` is injective on `K[X]`
over *any* commutative ring — and evaluation at `X = 0`, being a ring homomorphism, is compatible
with products and adjugates.

## Main results

* `mul_adjugate_mul_comm_of_sliceEntries`: the identity for an exact `n`-term decomposition.
* `zSliceMatrix_mul_adjugate_mul_comm`: the identity for a border-rank-`n` certificate.
* `normalizedSlices_commute_of_borderRankLE`: **Strassen's equations.**  If some slice `M_{z₀}` is
  invertible and `R̲(T) ≤ n`, then the normalized slices `M_{z₀}⁻¹ M_z` pairwise commute.
* `not_borderRankLE_of_normalizedSlices_ne` and `lt_borderRank_of_normalizedSlices_ne`: the
  contrapositive, packaged as the border-rank lower bound `R̲(T) ≥ n + 1`.

## Scope and non-goals

Only the *minimal* border-rank case is proved.  Strassen's full inequality
`2·(R̲(T) − n) ≥ rank [M_{z₀}⁻¹M_{z₁}, M_{z₀}⁻¹M_{z₂}]` is deliberately **not** claimed here: the
argument above degenerates for `r > n`, since the factorization `A · D · Bᵀ` needs square `A` and
`B`, and the general bound needs a different normal-form argument.  The minimal case is what the
`CW_q^σ` dichotomy of `Examples/GeneralizedCoppersmithWinogradStrassen.lean` consumes.

The statements are coordinate-level by design: slices are a basis-dependent presentation, and the
tensors that use them (`gcwTable`, matrix-multiplication coefficient tables) already live in
standard coordinates.  Nothing here needs a field: `K` is an arbitrary commutative ring.

## References

* [Strassen1983] V. Strassen, *Rank and optimal computation of generic tensors*, Linear Algebra
  Appl. 52/53 (1983) 645--685.
* [LandsbergOttaviani2013] J. M. Landsberg and G. Ottaviani, *Equations for secant varieties of
  Veronese and other varieties*, Ann. Mat. Pura Appl. 192 (2013).
-/

namespace AlgebraicComplexity.Tensor

open scoped Matrix Polynomial

universe u v

/-! ## The exact identity over a commutative ring -/

section ExactIdentity

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {ζ : Type*}

/-- **The division-free Strassen identity for an exact decomposition.**  If the `Z`-slices
`M_z : Matrix ι ι R` of a tensor are presented by `|ι|` pure terms,
`M_z p q = ∑_k a_k(p) · b_k(q) · c_k(z)`, then

`M_{z₁} · adj(M_{z₃}) · M_{z₂} = M_{z₂} · adj(M_{z₃}) · M_{z₁}`.

The term index is the *same* finite type as the two matrix legs; this is the minimal-rank
hypothesis, and the conclusion fails for more terms.

Proof sketch: collect the term vectors into square matrices `A p k = a_k p`, `B q k = b_k q`, so
that `M_z = A · diagonal(c_· z) · Bᵀ`.  The adjugate reverses products, so the middle factor
becomes `adj(Bᵀ) · adj(D_{z₃}) · adj(A)`; the two inner pairs collapse by `Bᵀ · adj(Bᵀ) = det B`
and `adj(A) · A = det A`, leaving `(det B · det A) · A · (D_{z₁} adj(D_{z₃}) D_{z₂}) · Bᵀ`.  All
three middle factors are diagonal, hence commute, so the expression is symmetric in `z₁` and
`z₂`. -/
theorem mul_adjugate_mul_comm_of_sliceEntries
    (a b : ι → ι → R) (c : ι → ζ → R) (M : ζ → Matrix ι ι R)
    (hM : ∀ z p q, M z p q = ∑ k, a k p * b k q * c k z) (z₁ z₂ z₃ : ζ) :
    M z₁ * (M z₃).adjugate * M z₂ = M z₂ * (M z₃).adjugate * M z₁ := by
  classical
  set A : Matrix ι ι R := Matrix.of fun p k ↦ a k p with hA
  set B : Matrix ι ι R := Matrix.of fun q k ↦ b k q with hB
  set D : ζ → Matrix ι ι R := fun z ↦ Matrix.diagonal fun k ↦ c k z with hD
  have hfac : ∀ z, M z = A * D z * Bᵀ := by
    intro z
    ext p q
    rw [hM, Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [hA, hB, hD, Matrix.of_apply, Matrix.diagonal_mul, Matrix.transpose_apply]
    ring
  have hBadj : ∀ Z : Matrix ι ι R, Bᵀ * ((Bᵀ).adjugate * Z) = B.det • Z := by
    intro Z
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.det_transpose, Matrix.smul_mul,
      Matrix.one_mul]
  have hAadj : ∀ Z : Matrix ι ι R, A.adjugate * (A * Z) = A.det • Z := by
    intro Z
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hdiag : D z₁ * ((D z₃).adjugate * (D z₂ * Bᵀ))
      = D z₂ * ((D z₃).adjugate * (D z₁ * Bᵀ)) := by
    simp only [← Matrix.mul_assoc]
    congr 1
    simp only [hD, Matrix.adjugate_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    ring
  rw [hfac z₁, hfac z₂, hfac z₃, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
  simp only [Matrix.mul_assoc, hBadj, hAadj, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [hdiag]

end ExactIdentity

/-! ## Coordinates of a polynomial leg vector -/

section LegPolynomial

variable {K : Type u} [CommRing K]

/-- The `K[X]`-coordinate of a polynomial leg vector: reading a polynomial path of vectors at a
fixed coordinate `p` gives an honest polynomial. -/
noncomputable def legPolynomial {ι : Type*} (v : PolynomialVector (ι → K)) (p : ι) : K[X] :=
  v.sum fun e f ↦ Polynomial.monomial e (f p)

/-- The `e`-th coefficient of `legPolynomial v p` is the `p`-th coordinate of the `e`-th
coefficient of `v`. -/
@[simp] theorem legPolynomial_coeff {ι : Type*} (v : PolynomialVector (ι → K)) (p : ι) (e : ℕ) :
    (legPolynomial v p).coeff e = v e p := by
  classical
  rw [legPolynomial, Finsupp.sum, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' v.support e fun e' ↦ v e' p]
  by_cases h : e ∈ v.support
  · simp [h]
  · have hv : v e = 0 := by simpa using h
    simp [h, hv]

/-- `legPolynomial` is additive in the polynomial path. -/
theorem legPolynomial_add {ι : Type*} (v w : PolynomialVector (ι → K)) (p : ι) :
    legPolynomial (v + w) p = legPolynomial v p + legPolynomial w p := by
  ext e
  simp

/-- `legPolynomial` sends the zero path to the zero polynomial. -/
@[simp] theorem legPolynomial_zero {ι : Type*} (p : ι) :
    legPolynomial (0 : PolynomialVector (ι → K)) p = 0 := by
  ext e
  simp

/-- `legPolynomial` sends a monomial path to the corresponding polynomial monomial. -/
@[simp] theorem legPolynomial_single {ι : Type*} (d : ℕ) (f : ι → K) (p : ι) :
    legPolynomial (Finsupp.single d f) p = Polynomial.monomial d (f p) := by
  ext e
  by_cases hde : d = e <;>
    simp [Polynomial.coeff_monomial, hde]

end LegPolynomial

/-! ## `Z`-slice matrices of a coordinate tensor -/

section Slices

variable {K : Type u} [CommRing K] {κ : Leg → Type v} [∀ i, Finite (κ i)]

/-- The `Z`-slice matrices of a tensor in standard finite coordinates.  The `Y`-leg index is
matched to the `X`-leg index through `eXY`, so that the slices are square and can be multiplied. -/
noncomputable def zSliceMatrix (eXY : κ .X ≃ κ .Y) (T : Tensor3 K (CoordinateSpace K κ))
    (z : κ .Z) : Matrix (κ .X) (κ .X) K :=
  Matrix.of fun p q ↦ standardCoordinateEquiv (K := K) (κ := κ) T (ofLegs p (eXY q) z)

/-- The entries of `zSliceMatrix` are the coefficients of the tensor. -/
@[simp] theorem zSliceMatrix_apply (eXY : κ .X ≃ κ .Y) (T : Tensor3 K (CoordinateSpace K κ))
    (z : κ .Z) (p q : κ .X) :
    zSliceMatrix eXY T z p q =
      standardCoordinateEquiv (K := K) (κ := κ) T (ofLegs p (eXY q) z) := rfl

/-- The coefficient bridge: the `e`-th coefficient of the product of the three `K[X]`-coordinates
of a polynomial pure tensor is the corresponding coordinate of the degree-`e` coefficient of the
polynomial pure path.

Proof sketch: both sides are additive in each of the three polynomial paths, so
`Finsupp.induction_linear` reduces to three monomial paths, where both sides are the same
`if`-guarded product of three scalars. -/
theorem coeff_legPolynomial_mul
    (u : PolynomialVector (CoordinateSpace K κ .X))
    (v : PolynomialVector (CoordinateSpace K κ .Y))
    (w : PolynomialVector (CoordinateSpace K κ .Z))
    (s : ∀ i, κ i) (e : ℕ) :
    (legPolynomial u (s .X) * legPolynomial v (s .Y) * legPolynomial w (s .Z)).coeff e =
      standardCoordinateEquiv (K := K) (κ := κ) (polynomialPure (K := K) (ofLegs u v w) e) s := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
      rw [legPolynomial_add, add_mul, add_mul, Polynomial.coeff_add, h₁, h₂,
        polynomialPure_add_X]
      simp
  | single dx ax =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ h₁ h₂ =>
          rw [legPolynomial_add, mul_add, add_mul, Polynomial.coeff_add, h₁, h₂,
            polynomialPure_add_Y]
          simp
      | single dy ay =>
          induction w using Finsupp.induction_linear with
          | zero => simp
          | add w₁ w₂ h₁ h₂ =>
              rw [legPolynomial_add, mul_add, Polynomial.coeff_add, h₁, h₂,
                polynomialPure_add_Z]
              simp
          | single dz az =>
              rw [legPolynomial_single, legPolynomial_single, legPolynomial_single,
                Polynomial.monomial_mul_monomial, Polynomial.monomial_mul_monomial,
                Polynomial.coeff_monomial]
              show _ = standardCoordinateEquiv (K := K) (κ := κ)
                (polynomialPure (K := K) (ofLegs (PolynomialVector.monomial dx ax)
                  (PolynomialVector.monomial dy ay) (PolynomialVector.monomial dz az)) e) s
              rw [polynomialPure_monomial]
              by_cases hd : dx + dy + dz = e
              · subst hd
                simp [PolynomialVector.monomial,
                  standardCoordinateEquiv_pure, prod_leg]
              · rw [if_neg hd,
                  PolynomialVector.monomial_coeff_of_ne (Ne.symm hd)
                    (pure (K := K) (ofLegs ax ay az)), map_zero]
                rfl

end Slices

/-! ## The identity at the border -/

section Border

variable {K : Type u} [CommRing K] {κ : Leg → Type v} [∀ i, Finite (κ i)]
variable [Fintype (κ .X)] [DecidableEq (κ .X)]

/-- Multiplication by `X ^ m` is injective on matrices over `K[X]`, over any commutative ring. -/
private theorem eq_of_smul_X_pow_eq {ι : Type*} (m : ℕ) {P Q : Matrix ι ι K[X]}
    (h : ((Polynomial.X : K[X]) ^ m) • P = ((Polynomial.X : K[X]) ^ m) • Q) : P = Q := by
  ext p q e
  have hpq := congrArg (fun M : Matrix ι ι K[X] ↦ M p q) h
  simp only [Matrix.smul_apply, smul_eq_mul] at hpq
  have hc := congrArg (fun r : K[X] ↦ r.coeff (e + m)) hpq
  simpa [Polynomial.coeff_X_pow_mul] using hc

/-- **Strassen's identity at the border.**  If the coordinate tensor `T` has a border-rank
certificate of size `n = |κ .X|`, then its `Z`-slices satisfy

`M_{z₁} · adj(M_{z₃}) · M_{z₂} = M_{z₂} · adj(M_{z₃}) · M_{z₁}`.

Proof sketch: a size-`n` border certificate is an exact `n`-term decomposition of a tensor over
`K[X]` whose leading coefficient in degree `d` is `T`.  Applying
`mul_adjugate_mul_comm_of_sliceEntries` over `K[X]` gives the identity for the polynomial slices
`M̃_z`.  Every entry of `M̃_z` is divisible by `X^d`, so `M̃_z = X^d • N_z`; homogeneity of the
adjugate (`Matrix.adjugate_smul`) makes both sides of the identity `X^{d(n+1)}` times the same
expression in the `N_z`, and multiplication by that power of `X` is injective.  Evaluation at
`X = 0` is a ring homomorphism, so it commutes with products and adjugates
(`RingHom.map_adjugate`), and it sends `N_z` to the slice `M_z` of the leading tensor. -/
theorem zSliceMatrix_mul_adjugate_mul_comm (eXY : κ .X ≃ κ .Y)
    {T : Tensor3 K (CoordinateSpace K κ)} (h : BorderRankLE (Fintype.card (κ .X)) T)
    (z₁ z₂ z₃ : κ .Z) :
    zSliceMatrix eXY T z₁ * (zSliceMatrix eXY T z₃).adjugate * zSliceMatrix eXY T z₂ =
      zSliceMatrix eXY T z₂ * (zSliceMatrix eXY T z₃).adjugate * zSliceMatrix eXY T z₁ := by
  classical
  obtain ⟨d, terms, hlen, hlead⟩ := h
  obtain ⟨F, hF⟩ : ∃ F : ℕ → (∀ i, PolynomialVector (CoordinateSpace K κ i)),
      ∀ i, F i = if hi : i < terms.length then terms.get ⟨i, hi⟩ else fun _ ↦ 0 :=
    ⟨_, fun _ ↦ rfl⟩
  have hpure0 : polynomialPure (K := K) (V := CoordinateSpace K κ) (fun _ ↦ 0) = 0 := by
    have hz : (fun _ ↦ 0 : ∀ i, PolynomialVector (CoordinateSpace K κ i)) =
        ofLegs (0 : PolynomialVector (CoordinateSpace K κ .X))
          (0 : PolynomialVector (CoordinateSpace K κ .Y))
          (0 : PolynomialVector (CoordinateSpace K κ .Z)) := by
      funext i; cases i <;> rfl
    rw [hz]
    exact polynomialPure_zero_X (K := K) (V := CoordinateSpace K κ) 0 0
  set idx : κ .X ≃ Fin (Fintype.card (κ .X)) := Fintype.equivFin (κ .X) with hidx
  have hsum : ∑ k : κ .X, polynomialPure (K := K) (F (idx k)) =
      (terms.map (polynomialPure (K := K))).sum := by
    have h1 : ∑ k : κ .X, polynomialPure (K := K) (F (idx k)) =
        ∑ j : Fin (Fintype.card (κ .X)), polynomialPure (K := K) (F j) :=
      Fintype.sum_equiv idx _ _ fun _ ↦ rfl
    have h2 : ∑ j : Fin (Fintype.card (κ .X)), polynomialPure (K := K) (F j) =
        ∑ i ∈ Finset.range (Fintype.card (κ .X)), polynomialPure (K := K) (F i) :=
      Fin.sum_univ_eq_sum_range (fun i ↦ polynomialPure (K := K) (F i)) _
    have h3 : ∑ i ∈ Finset.range terms.length, polynomialPure (K := K) (F i) =
        ∑ i ∈ Finset.range (Fintype.card (κ .X)), polynomialPure (K := K) (F i) := by
      have hsub : Finset.range terms.length ⊆ Finset.range (Fintype.card (κ .X)) :=
        Finset.range_subset_range.mpr hlen
      refine Finset.sum_subset hsub fun i _ hi ↦ ?_
      have hi' : ¬ i < terms.length := by simpa using hi
      rw [hF, dif_neg hi', hpure0]
    have h4 : (terms.map (polynomialPure (K := K))).sum =
        ∑ i ∈ Finset.range terms.length, polynomialPure (K := K) (F i) := by
      rw [list_map_sum_eq_fin_sum, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hF, dif_pos j.isLt]
    rw [h1, h2, ← h3, ← h4]
  obtain ⟨Mt, hMt⟩ : ∃ Mt : κ .Z → Matrix (κ .X) (κ .X) K[X], ∀ z p q, Mt z p q =
      ∑ k : κ .X, legPolynomial (F (idx k) .X) p * legPolynomial (F (idx k) .Y) (eXY q) *
        legPolynomial (F (idx k) .Z) z :=
    ⟨fun z ↦ Matrix.of fun p q ↦ _, fun _ _ _ ↦ rfl⟩
  have hstep := mul_adjugate_mul_comm_of_sliceEntries
    (a := fun k p ↦ legPolynomial (F (idx k) .X) p)
    (b := fun k q ↦ legPolynomial (F (idx k) .Y) (eXY q))
    (c := fun k z ↦ legPolynomial (F (idx k) .Z) z) Mt hMt z₁ z₂ z₃
  have hcoeff : ∀ (z : κ .Z) (p q : κ .X) (e : ℕ), (Mt z p q).coeff e =
      standardCoordinateEquiv (K := K) (κ := κ)
        ((terms.map (polynomialPure (K := K))).sum e) (ofLegs p (eXY q) z) := by
    intro z p q e
    rw [hMt, Polynomial.finsetSum_coeff, ← hsum]
    have hterm : ∀ k : κ .X,
        (legPolynomial (F (idx k) .X) p * legPolynomial (F (idx k) .Y) (eXY q) *
          legPolynomial (F (idx k) .Z) z).coeff e =
        standardCoordinateEquiv (K := K) (κ := κ) (polynomialPure (K := K) (F (idx k)) e)
          (ofLegs p (eXY q) z) := by
      intro k
      have hb := coeff_legPolynomial_mul (K := K) (κ := κ)
        (F (idx k) .X) (F (idx k) .Y) (F (idx k) .Z) (ofLegs p (eXY q) z) e
      simpa using hb
    have hRHS : standardCoordinateEquiv (K := K) (κ := κ)
          ((∑ k : κ .X, polynomialPure (K := K) (F (idx k))) e) (ofLegs p (eXY q) z) =
        ∑ k : κ .X, standardCoordinateEquiv (K := K) (κ := κ)
          (polynomialPure (K := K) (F (idx k)) e) (ofLegs p (eXY q) z) := by
      rw [Finsupp.finsetSum_apply, map_sum, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun k _ ↦ hterm k, hRHS]
  have hdvd : ∀ (z : κ .Z) (p q : κ .X), (Polynomial.X : K[X]) ^ d ∣ Mt z p q := by
    intro z p q
    rw [Polynomial.X_pow_dvd_iff]
    intro e he
    rw [hcoeff, hlead.lower_coeff he]
    simp
  choose N hN using hdvd
  obtain ⟨NN, hNN⟩ : ∃ NN : κ .Z → Matrix (κ .X) (κ .X) K[X], ∀ z p q, NN z p q = N z p q :=
    ⟨fun z ↦ Matrix.of fun p q ↦ N z p q, fun _ _ _ ↦ rfl⟩
  have hMtN : ∀ z, Mt z = ((Polynomial.X : K[X]) ^ d) • NN z := by
    intro z
    ext p q
    rw [Matrix.smul_apply, smul_eq_mul, hNN, hN]
  have hNeval : ∀ z, ((Polynomial.evalRingHom (0 : K)).mapMatrix) (NN z) =
      zSliceMatrix eXY T z := by
    intro z
    ext p q
    have h0 : (N z p q).coeff 0 = (Mt z p q).coeff d := by
      rw [hN z p q, ← Polynomial.coeff_X_pow_mul (N z p q) d 0, zero_add]
    have h1 : (Mt z p q).coeff d = zSliceMatrix eXY T z p q := by
      rw [hcoeff, hlead.coeff]
      rfl
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hNN, Polynomial.coe_evalRingHom,
      ← Polynomial.coeff_zero_eq_eval_zero, h0, h1]
  have hexp : ∀ w₁ w₂ : κ .Z, Mt w₁ * (Mt z₃).adjugate * Mt w₂ =
      ((Polynomial.X : K[X]) ^ (d + (d * (Fintype.card (κ .X) - 1) + d))) •
        (NN w₁ * (NN z₃).adjugate * NN w₂) := by
    intro w₁ w₂
    rw [hMtN w₁, hMtN w₂, hMtN z₃, Matrix.adjugate_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_mul, ← pow_add]
  rw [hexp z₁ z₂, hexp z₂ z₁] at hstep
  have hfinal := congrArg
    (fun M : Matrix (κ .X) (κ .X) K[X] ↦ ((Polynomial.evalRingHom (0 : K)).mapMatrix) M)
    (eq_of_smul_X_pow_eq _ hstep)
  simpa only [map_mul, RingHom.map_adjugate, hNeval] using hfinal

/-- **Strassen's commutation equations.**  Let `T` be a coordinate tensor whose `Z`-slices are
square of size `n = |κ .X|`, and suppose one slice `M_{z₀}` is invertible with inverse `Q`.  If
`T` has *minimal* border rank, `R̲(T) ≤ n`, then the normalized slices `A_z = Q · M_z` pairwise
commute.

Proof sketch: `zSliceMatrix_mul_adjugate_mul_comm` at `z₃ = z₀` gives
`M_{z₁} adj(M_{z₀}) M_{z₂} = M_{z₂} adj(M_{z₀}) M_{z₁}`.  Because `M_{z₀} · Q = 1`, the adjugate is
`adj(M_{z₀}) = det(M_{z₀}) • Q`, and `det(M_{z₀})` is a unit with inverse `det Q`, so the scalar
cancels: `M_{z₁} Q M_{z₂} = M_{z₂} Q M_{z₁}`.  Multiplying on the left by `Q` is the claim. -/
theorem normalizedSlices_commute_of_borderRankLE (eXY : κ .X ≃ κ .Y)
    {T : Tensor3 K (CoordinateSpace K κ)} (h : BorderRankLE (Fintype.card (κ .X)) T)
    {z₀ : κ .Z} {Q : Matrix (κ .X) (κ .X) K}
    (hQ : zSliceMatrix eXY T z₀ * Q = 1) (z₁ z₂ : κ .Z) :
    Q * zSliceMatrix eXY T z₁ * (Q * zSliceMatrix eXY T z₂) =
      Q * zSliceMatrix eXY T z₂ * (Q * zSliceMatrix eXY T z₁) := by
  have hadj : (zSliceMatrix eXY T z₀).adjugate = (zSliceMatrix eXY T z₀).det • Q := by
    calc (zSliceMatrix eXY T z₀).adjugate
        = (zSliceMatrix eXY T z₀).adjugate * (zSliceMatrix eXY T z₀ * Q) := by
          rw [hQ, Matrix.mul_one]
      _ = ((zSliceMatrix eXY T z₀).adjugate * zSliceMatrix eXY T z₀) * Q := by
          rw [Matrix.mul_assoc]
      _ = ((zSliceMatrix eXY T z₀).det • (1 : Matrix (κ .X) (κ .X) K)) * Q := by
          rw [Matrix.adjugate_mul]
      _ = (zSliceMatrix eXY T z₀).det • Q := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hdet : (zSliceMatrix eXY T z₀).det * Q.det = 1 := by
    rw [← Matrix.det_mul, hQ, Matrix.det_one]
  have key := zSliceMatrix_mul_adjugate_mul_comm eXY h z₁ z₂ z₀
  rw [hadj] at key
  have key1 : (zSliceMatrix eXY T z₀).det •
        (zSliceMatrix eXY T z₁ * Q * zSliceMatrix eXY T z₂) =
      (zSliceMatrix eXY T z₀).det • (zSliceMatrix eXY T z₂ * Q * zSliceMatrix eXY T z₁) := by
    simpa only [Matrix.smul_mul, Matrix.mul_smul] using key
  have key2 : zSliceMatrix eXY T z₁ * Q * zSliceMatrix eXY T z₂ =
      zSliceMatrix eXY T z₂ * Q * zSliceMatrix eXY T z₁ := by
    have hq := congrArg (fun A : Matrix (κ .X) (κ .X) K ↦ Q.det • A) key1
    simpa only [smul_smul, mul_comm Q.det, hdet, one_smul] using hq
  calc Q * zSliceMatrix eXY T z₁ * (Q * zSliceMatrix eXY T z₂)
      = Q * (zSliceMatrix eXY T z₁ * Q * zSliceMatrix eXY T z₂) := by
        simp only [Matrix.mul_assoc]
    _ = Q * (zSliceMatrix eXY T z₂ * Q * zSliceMatrix eXY T z₁) := by rw [key2]
    _ = Q * zSliceMatrix eXY T z₂ * (Q * zSliceMatrix eXY T z₁) := by
        simp only [Matrix.mul_assoc]

/-- The contrapositive of Strassen's equations: two non-commuting normalized slices rule out a
border-rank certificate of the minimal size `|κ .X|`. -/
theorem not_borderRankLE_of_normalizedSlices_ne (eXY : κ .X ≃ κ .Y)
    (T : Tensor3 K (CoordinateSpace K κ))
    {z₀ : κ .Z} {Q : Matrix (κ .X) (κ .X) K} (hQ : zSliceMatrix eXY T z₀ * Q = 1)
    {z₁ z₂ : κ .Z}
    (hne : Q * zSliceMatrix eXY T z₁ * (Q * zSliceMatrix eXY T z₂) ≠
      Q * zSliceMatrix eXY T z₂ * (Q * zSliceMatrix eXY T z₁)) :
    ¬ BorderRankLE (Fintype.card (κ .X)) T := fun h ↦
  hne (normalizedSlices_commute_of_borderRankLE eXY h hQ z₁ z₂)

/-- Numerical form of the previous theorem: two non-commuting normalized slices force
`R̲(T) ≥ |κ .X| + 1`. -/
theorem lt_borderRank_of_normalizedSlices_ne (eXY : κ .X ≃ κ .Y)
    (T : Tensor3 K (CoordinateSpace K κ))
    {z₀ : κ .Z} {Q : Matrix (κ .X) (κ .X) K} (hQ : zSliceMatrix eXY T z₀ * Q = 1)
    {z₁ z₂ : κ .Z}
    (hne : Q * zSliceMatrix eXY T z₁ * (Q * zSliceMatrix eXY T z₂) ≠
      Q * zSliceMatrix eXY T z₂ * (Q * zSliceMatrix eXY T z₁)) :
    Fintype.card (κ .X) < borderRank T := by
  refine lt_of_not_ge fun hle ↦ ?_
  exact not_borderRankLE_of_normalizedSlices_ne eXY T hQ hne (borderRank_le_iff.mp hle)

end Border

end AlgebraicComplexity.Tensor
