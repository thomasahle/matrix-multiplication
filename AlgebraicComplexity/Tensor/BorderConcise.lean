/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Concise
import AlgebraicComplexity.Tensor.BorderRank
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Border-rank lower bounds from conciseness

This file proves the border-rank analogue of the flattening lower bounds of `Tensor/Concise.lean`:
a tensor that is concise in one leg has border rank at least the dimension of that leg.  This is
Theorem 3.4 of He and Williams's CS 6810 notes (see `DESIGN.md`; the notes are a roadmap, not the
normative source, and the statement proved here is the standard degeneration-stable lower bound).

## Main results

* `PolynomialVector.convolution_lsmul_mem_span_shift`: convolving a fixed polynomial vector `u`
  with a scalar polynomial of degree at most `D` lands in the span of the shifts
  `ε^e • u` for `e ≤ D`;
* `linearIndependent_shift_of_hasLeadingTerm`: shifted copies `ε^k Q_i`, `k < m`, of polynomial
  vectors whose degree-`d` leading coefficients are linearly independent are themselves linearly
  independent;
* `finrank_le_of_leadingTerm_span_shift`: the leading-coefficient extraction lemma.  If a family
  of polynomial vectors lies in the span of the shifts of `ℓ` generators, vanishes below degree
  `d`, and has degree-`d` coefficients spanning a module `M`, then `finrank M ≤ ℓ`;
* `BorderRankLE.finrank_X_le` (and the `Y`, `Z`, and `max` versions): a constructive border-rank
  certificate of size `r` for a tensor that is `X`-concise forces `finrank (V .X) ≤ r`;
* `BorderRankLEAt.finrank_X_le` and friends: the same bounds from degree-aware certificates;
* `finrank_X_le_borderRank` and friends: the numeric `borderRank` corollaries.

## Layer placement and strategy

The first two sections are generic polynomial-vector algebra and belong to the tensor layer's
constructive-degeneration toolkit; they mention no tensors.  The final section combines them with
the dual-contraction formulation of conciseness from `Tensor/Concise.lean`.

Proof strategy.  A border-rank certificate exhibits the tensor `T` as the degree-`d` leading
coefficient of `P = ∑_{j<ℓ} polynomialPure (x_j)` with `ℓ ≤ r`.  Contracting the `Y` and `Z` legs
of the path `P` by dual vectors `(f_Y, f_Z)`, coefficientwise, produces a polynomial vector in
`(V .X)[ε]` equal to `∑_j s_j ⋆ (x_j .X)` for scalar polynomials `s_j` of degree bounded by the
certificate (`mapLinear_contractX_polynomialPure`), hence lying in the span of boundedly many
shifts of the `ℓ` fixed polynomial vectors `x_j .X`.  Its degree-`d` coefficient is the
corresponding contraction of `T`.  If `finrank (V .X) > ℓ`, conciseness produces
`n = ℓ + 1` contraction paths whose leading coefficients are linearly independent; the shifted
family `ε^k Q_i` with `k < m` is then linearly independent (extract coefficients from the lowest
shift upward), giving `n·m` independent vectors inside the span of the `ℓ·(D + m)` generators
`ε^e • x_j .X`.  For `m` large this contradicts the strong rank condition
(`linearIndependent_le_span'`).  This replaces the classical "all `(r+1)`-minors of a sum of `r`
dyads vanish" argument by a basis-free counting argument over the coefficient field, avoiding
determinants entirely.

## Non-goals

Lower semicontinuity of flattening ranks in a topological sense is not formalized; the present
route is purely algebraic and works over the field hypotheses already used by `Tensor/Concise`.
The abstract extraction lemmas are stated over a commutative ring satisfying the strong rank
condition so they remain usable beyond fields.
-/

namespace AlgebraicComplexity.Tensor

universe u v

/-! ### Shift-and-convolution algebra for polynomial vectors -/

section ShiftAlgebra

variable {K : Type u} [CommSemiring K]

namespace PolynomialVector

/-- Composing two shifts multiplies the pure monomial `ε^a • ε^b` into `ε^(a+b)`. -/
theorem shift_shift {M : Type*} [AddCommMonoid M] (a b : ℕ) (P : PolynomialVector M) :
    shift a (shift b P) = shift (a + b) P := by
  show Finsupp.mapDomain (fun e ↦ a + e) (Finsupp.mapDomain (fun e ↦ b + e) P) =
    Finsupp.mapDomain (fun e ↦ a + b + e) P
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext e
  simp only [Function.comp_apply]
  omega

variable {M : Type*} [AddCommMonoid M] [Module K M]

/-- Multiplication by `ε^n`, packaged as a linear map on polynomial vectors. -/
noncomputable def shiftLinear (n : ℕ) : PolynomialVector M →ₗ[K] PolynomialVector M where
  toFun := shift n
  map_add' := shift_add n
  map_smul' r P := shift_smul n r P

@[simp] theorem shiftLinear_apply (n : ℕ) (P : PolynomialVector M) :
    shiftLinear (K := K) n P = shift n P := rfl

/-- Coefficientwise application of a linear map cannot enlarge the support. -/
theorem support_mapLinear_subset {N : Type*} [AddCommMonoid N] [Module K N]
    (f : M →ₗ[K] N) (P : PolynomialVector M) :
    (mapLinear f P).support ⊆ P.support := by
  intro e he
  rw [Finsupp.mem_support_iff] at he ⊢
  intro h0
  exact he (by rw [mapLinear_apply, h0, map_zero])

/-- A convolution coefficient beyond the sum of the two degree bounds vanishes. -/
theorem convolution_apply_eq_zero_of_lt
    {N P : Type*} [AddCommMonoid N] [Module K N] [AddCommMonoid P] [Module K P]
    (B : M →ₗ[K] N →ₗ[K] P) {f : PolynomialVector M} {g : PolynomialVector N}
    {Df Dg : ℕ} (hf : ∀ i ∈ f.support, i ≤ Df) (hg : ∀ j ∈ g.support, j ≤ Dg)
    {n : ℕ} (hn : Df + Dg < n) :
    convolution B f g n = 0 := by
  classical
  rw [convolution_coeff]
  refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun j hj ↦ ?_
  have hij : i + j ≠ n := by
    have h1 := hf i hi
    have h2 := hg j hj
    omega
  simp [hij]

/-- Convolution with a scalar polynomial is the corresponding combination of shifts:
`s ⋆ u = ∑_e s_e • (ε^e • u)`. -/
theorem convolution_lsmul (s : PolynomialVector K) (u : PolynomialVector M) :
    convolution (LinearMap.lsmul K M) s u = s.sum fun e c ↦ c • shift e u := by
  classical
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [convolution_add_left, ha, hb,
        Finsupp.sum_add_index' (fun e ↦ by simp) (fun e c₁ c₂ ↦ by rw [add_smul])]
  | single e c =>
      change convolution (LinearMap.lsmul K M) (monomial e c) u =
        (Finsupp.single e c).sum fun e' c' ↦ c' • shift e' u
      rw [Finsupp.sum_single_index (by simp)]
      induction u using Finsupp.induction_linear with
      | zero => simp
      | add u₁ u₂ h₁ h₂ => rw [convolution_add_right, h₁, h₂, shift_add, smul_add]
      | single j y =>
          change convolution (LinearMap.lsmul K M) (monomial e c) (monomial j y) =
            c • shift e (monomial j y)
          rw [convolution_monomial, shift_monomial]
          simp

/-- Convolving `u` with a scalar polynomial supported in degrees at most `D` lands in the span
of the finitely many shifts `ε^e • u` with `e ≤ D`. -/
theorem convolution_lsmul_mem_span_shift (s : PolynomialVector K) (u : PolynomialVector M)
    {D : ℕ} (hs : ∀ e ∈ s.support, e ≤ D) :
    convolution (LinearMap.lsmul K M) s u ∈
      Submodule.span K (Set.range fun e : Fin (D + 1) ↦ shift (e : ℕ) u) := by
  classical
  rw [convolution_lsmul]
  apply Submodule.sum_mem
  intro e he
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨e, Nat.lt_succ_of_le (hs e he)⟩, rfl⟩)

end PolynomialVector

end ShiftAlgebra

/-! ### Leading-coefficient extraction -/

section LeadingCoefficient

variable {K : Type u} [CommRing K] {M : Type v} [AddCommGroup M] [Module K M]

open PolynomialVector

/-- Shifted copies of polynomial vectors with linearly independent leading coefficients are
linearly independent.

`Q i` has all coefficients below `d` equal to zero and degree-`d` coefficient `w i`; the family
of all shifts `ε^k • Q i` with `k < m` is then linearly independent whenever the `w i` are.

Proof sketch: in a vanishing combination, extract the coefficient of degree `d + k` for
`k = 0, 1, …` in turn.  Shifts by more than `k` contribute nothing in this degree because the
`Q i` vanish below `d`, shifts by less than `k` have zero coefficients by induction, and the
shift by exactly `k` contributes `∑ i, g (i, k) • w i`, so independence of the `w i` kills the
`k`-th layer of coefficients. -/
theorem linearIndependent_shift_of_hasLeadingTerm
    {ι : Type*} [Fintype ι] {w : ι → M} (hw : LinearIndependent K w)
    {Q : ι → PolynomialVector M} {d : ℕ}
    (hQ : ∀ i, HasLeadingTerm (Q i) d (w i)) (m : ℕ) :
    LinearIndependent K fun p : ι × Fin m ↦
      PolynomialVector.shift (p.2 : ℕ) (Q p.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ k, ∀ hk : k < m, ∀ i : ι, g (i, ⟨k, hk⟩) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
      intro hk i
      -- extract the coefficient in degree `d + k` from the vanishing combination
      have h0 : (Finsupp.lapply (d + k) : PolynomialVector M →ₗ[K] M)
          (∑ p : ι × Fin m, g p • PolynomialVector.shift (p.2 : ℕ) (Q p.1)) = 0 := by
        rw [hg, map_zero]
      rw [map_sum] at h0
      simp only [map_smul, Finsupp.lapply_apply] at h0
      rw [Fintype.sum_prod_type] at h0
      have hinner : ∀ i' : ι,
          (∑ k' : Fin m,
            g (i', k') • (PolynomialVector.shift (k' : ℕ) (Q i')) (d + k)) =
            g (i', ⟨k, hk⟩) • w i' := by
        intro i'
        have hmain :
            (∑ k' : Fin m,
              g (i', k') • (PolynomialVector.shift (k' : ℕ) (Q i')) (d + k)) =
              g (i', ⟨k, hk⟩) •
                (PolynomialVector.shift ((⟨k, hk⟩ : Fin m) : ℕ) (Q i')) (d + k) :=
          Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (fun k' _ hne ↦ by
            rcases Nat.lt_trichotomy (k' : ℕ) k with hlt | heq | hgt
            · have hzero : g (i', k') = 0 := IH (k' : ℕ) hlt k'.isLt i'
              rw [hzero, zero_smul]
            · exact absurd (Fin.ext heq) hne
            · rw [PolynomialVector.shift_apply]
              by_cases hle : (k' : ℕ) ≤ d + k
              · rw [if_pos hle, (hQ i').lower_coeff (by omega), smul_zero]
              · rw [if_neg hle, smul_zero])
        have hval : ((⟨k, hk⟩ : Fin m) : ℕ) = k := rfl
        rw [hmain, hval, PolynomialVector.shift_apply,
          if_pos (Nat.le_add_left k d), show d + k - k = d from by omega,
          (hQ i').coeff]
      have hsum := (Finset.sum_congr rfl fun i' _ ↦ hinner i').symm.trans h0
      exact Fintype.linearIndependent_iff.mp hw _ hsum i
  intro p
  exact key (p.2 : ℕ) p.2.isLt p.1

/-- Polynomial vectors whose coefficients vanish in all degrees below `d` form a submodule. -/
private def vanishBelow (K : Type u) [CommRing K] (M : Type v) [AddCommGroup M] [Module K M]
    (d : ℕ) : Submodule K (PolynomialVector M) where
  carrier := {P | ∀ e < d, P e = 0}
  add_mem' := fun {a b} ha hb e he ↦ by
    rw [Finsupp.add_apply, ha e he, hb e he, add_zero]
  zero_mem' := fun e _ ↦ rfl
  smul_mem' := fun c {P} hP e he ↦ by
    rw [Finsupp.smul_apply, hP e he, smul_zero]

private theorem mem_vanishBelow {d : ℕ} {P : PolynomialVector M} :
    P ∈ vanishBelow K M d ↔ ∀ e < d, P e = 0 := Iff.rfl

variable [StrongRankCondition K]

/-- The counting core: a finite family with linearly independent images under leading-coefficient
extraction, all of whose certificate paths lie in the span of `ℓ` generators and their shifts up
to degree `D`, has at most `ℓ` members.

Proof sketch: choose a lifted path `Q i` for each `w i`.  For every `m`, the shifted family
`ε^k • Q i` with `k < m` is linearly independent by `linearIndependent_shift_of_hasLeadingTerm`,
and lies in the span of the `ℓ·(D + m)` vectors `ε^e • u j` with `e < D + m`.  The strong rank
condition gives `n·m ≤ ℓ·(D + m)` for every `m`; taking `m = ℓ·D + ℓ + 1` forces `n ≤ ℓ`. -/
private theorem card_le_of_linearIndependent_leadingTerm
    {ι : Type*} [Fintype ι] {w : ι → M} (hw : LinearIndependent K w)
    {d ℓ D : ℕ} {u : Fin ℓ → PolynomialVector M}
    (hlift : ∀ x : M, ∃ Q : PolynomialVector M,
      Q ∈ Submodule.span K (Set.range fun p : Fin ℓ × Fin (D + 1) ↦
        PolynomialVector.shift (p.2 : ℕ) (u p.1)) ∧ HasLeadingTerm Q d x) :
    Fintype.card ι ≤ ℓ := by
  classical
  choose Q hQmem hQlead using fun i ↦ hlift (w i)
  set m : ℕ := ℓ * D + ℓ + 1 with hm
  have hindep : LinearIndependent K
      fun p : ι × Fin m ↦ PolynomialVector.shift (p.2 : ℕ) (Q p.1) :=
    linearIndependent_shift_of_hasLeadingTerm hw hQlead m
  have hrange :
      Set.range (fun p : ι × Fin m ↦ PolynomialVector.shift (p.2 : ℕ) (Q p.1)) ⊆
        ↑(Submodule.span K (Set.range fun p : Fin ℓ × Fin (D + m) ↦
          PolynomialVector.shift (p.2 : ℕ) (u p.1))) := by
    rintro _ ⟨⟨i, k⟩, rfl⟩
    have h1 : PolynomialVector.shiftLinear (K := K) (k : ℕ) (Q i) ∈
        Submodule.map (PolynomialVector.shiftLinear (K := K) (k : ℕ))
          (Submodule.span K (Set.range fun p : Fin ℓ × Fin (D + 1) ↦
            PolynomialVector.shift (p.2 : ℕ) (u p.1))) :=
      Submodule.mem_map_of_mem (hQmem i)
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨⟨j, e⟩, rfl⟩, rfl⟩
    refine ⟨(j, ⟨(k : ℕ) + (e : ℕ), ?_⟩), ?_⟩
    · have hkm := k.isLt
      have heD := e.isLt
      omega
    · simp only [PolynomialVector.shiftLinear_apply]
      exact (PolynomialVector.shift_shift (k : ℕ) (e : ℕ) (u j)).symm
  have hcard := linearIndependent_le_span' _ hindep _ hrange
  rw [Cardinal.mk_fintype, Nat.cast_le] at hcard
  have hcard2 : Fintype.card (ι × Fin m) ≤ Fintype.card (Fin ℓ × Fin (D + m)) :=
    hcard.trans (Fintype.card_range_le _)
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard2
  by_contra hn
  have hn' : ℓ + 1 ≤ Fintype.card ι := Nat.lt_of_not_le hn
  have hstep : (ℓ + 1) * m ≤ ℓ * (D + m) :=
    le_trans (Nat.mul_le_mul_right m hn') hcard2
  have hexp : m + ℓ * m ≤ ℓ * D + ℓ * m := by
    calc m + ℓ * m = (ℓ + 1) * m := by ring
    _ ≤ ℓ * (D + m) := hstep
    _ = ℓ * D + ℓ * m := by ring
  have hmle : m ≤ ℓ * D := Nat.le_of_add_le_add_right hexp
  rw [hm] at hmle
  exact absurd hmle (by
    apply Nat.not_le.mpr
    calc ℓ * D < ℓ * D + (ℓ + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos ℓ)
    _ = ℓ * D + ℓ + 1 := by ring)

/-- Leading-coefficient extraction.  If every member of a family of polynomial vectors lies in
the span of the shifts (up to degree `D`) of `ℓ` fixed generators, vanishes below degree `d`,
and the degree-`d` coefficients span `M`, then `finrank M ≤ ℓ`.

This is the abstract engine behind the border-rank conciseness bounds: `A q` will be a
contraction of a border-rank certificate path, and `v q` the corresponding contraction of the
limit tensor.  It is stated at the generality the *second* intended consumer needs — arbitrary
`M`, arbitrary index family, a ring with the strong rank condition — namely the border-rank
upgrade of the Koszul flattening; see the "Non-goals and the border-rank obstruction" section of
`Tensor/KoszulFlattening.lean` for the one missing input (a `K[ε]`-generation count), which is
the only thing standing between this engine and that bound.

Proof sketch: the admissible paths form a submodule mapped onto `M` by the degree-`d`
coefficient map, so every element of `M` lifts to an admissible path.  Every finite linearly
independent family of `M` therefore lifts to certificate paths, and
`card_le_of_linearIndependent_leadingTerm` bounds its size by `ℓ`; `rank_le` converts this
uniform bound into `finrank M ≤ ℓ`. -/
theorem finrank_le_of_leadingTerm_span_shift
    {ι : Type*} {A : ι → PolynomialVector M} {v : ι → M} {d ℓ D : ℕ}
    {u : Fin ℓ → PolynomialVector M}
    (hlow : ∀ q, ∀ e < d, A q e = 0)
    (hcoeff : ∀ q, A q d = v q)
    (hmem : ∀ q, A q ∈ Submodule.span K (Set.range fun p : Fin ℓ × Fin (D + 1) ↦
      PolynomialVector.shift (p.2 : ℕ) (u p.1)))
    (hspan : Submodule.span K (Set.range v) = ⊤) :
    Module.finrank K M ≤ ℓ := by
  classical
  have hlift : ∀ x : M, ∃ Q : PolynomialVector M,
      Q ∈ Submodule.span K (Set.range fun p : Fin ℓ × Fin (D + 1) ↦
        PolynomialVector.shift (p.2 : ℕ) (u p.1)) ∧ HasLeadingTerm Q d x := by
    intro x
    have htop : Submodule.map (Finsupp.lapply (R := K) d)
        (Submodule.span K (Set.range fun p : Fin ℓ × Fin (D + 1) ↦
          PolynomialVector.shift (p.2 : ℕ) (u p.1)) ⊓ vanishBelow K M d) = ⊤ := by
      apply le_antisymm le_top
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      refine Submodule.mem_map.mpr
        ⟨A q, Submodule.mem_inf.mpr ⟨hmem q, mem_vanishBelow.mpr (hlow q)⟩, ?_⟩
      rw [Finsupp.lapply_apply]
      exact hcoeff q
    have hx : x ∈ Submodule.map (Finsupp.lapply (R := K) d)
        (Submodule.span K (Set.range fun p : Fin ℓ × Fin (D + 1) ↦
          PolynomialVector.shift (p.2 : ℕ) (u p.1)) ⊓ vanishBelow K M d) := by
      rw [htop]
      exact Submodule.mem_top
    rcases Submodule.mem_map.mp hx with ⟨Q, hQ, hQx⟩
    rcases Submodule.mem_inf.mp hQ with ⟨hQspan, hQlow⟩
    refine ⟨Q, hQspan, ?_, mem_vanishBelow.mp hQlow⟩
    rw [← hQx, Finsupp.lapply_apply]
  apply Module.finrank_le_of_rank_le
  apply rank_le
  intro s hs
  have hcard := card_le_of_linearIndependent_leadingTerm hs hlift
  simpa using hcard

end LeadingCoefficient

/-! ### Border-rank conciseness bounds -/

section BorderConciseness

variable {K : Type u} [Field K]
variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

open PolynomialVector

/-- Contracting the `Y` and `Z` legs of a polynomial pure tensor, coefficient by coefficient,
convolves the `X` polynomial vector with the scalar polynomial obtained by pairing the dual
vectors with the `Y` and `Z` polynomial vectors.  Explicit three-leg form. -/
private theorem mapLinear_contractX_polynomialPure_ofLegs
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K)
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) :
    PolynomialVector.mapLinear (contractX fy fz)
        (polynomialPure (K := K) (ofLegs xX xY xZ)) =
      PolynomialVector.convolution (LinearMap.lsmul K (V .X))
        (PolynomialVector.convolution (LinearMap.lsmul K K)
          (PolynomialVector.mapLinear fy xY) (PolynomialVector.mapLinear fz xZ)) xX := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp [polynomialPure_add_X, map_add, ha, hb,
        PolynomialVector.convolution_add_right]
  | single dx vx =>
      induction xY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp [polynomialPure_add_Y, map_add, ha, hb,
            PolynomialVector.convolution_add_left]
      | single dy vy =>
          induction xZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp [polynomialPure_add_Z, map_add, ha, hb,
                PolynomialVector.convolution_add_left,
                PolynomialVector.convolution_add_right]
          | single dz vz =>
              change PolynomialVector.mapLinear (contractX fy fz)
                  (polynomialPure (K := K) (ofLegs
                    (PolynomialVector.monomial dx vx)
                    (PolynomialVector.monomial dy vy)
                    (PolynomialVector.monomial dz vz))) =
                PolynomialVector.convolution (LinearMap.lsmul K (V .X))
                  (PolynomialVector.convolution (LinearMap.lsmul K K)
                    (PolynomialVector.mapLinear fy (PolynomialVector.monomial dy vy))
                    (PolynomialVector.mapLinear fz (PolynomialVector.monomial dz vz)))
                  (PolynomialVector.monomial dx vx)
              rw [polynomialPure_monomial, PolynomialVector.mapLinear_monomial,
                PolynomialVector.mapLinear_monomial, PolynomialVector.mapLinear_monomial,
                PolynomialVector.convolution_monomial,
                PolynomialVector.convolution_monomial,
                show dy + dz + dx = dx + dy + dz from by omega]
              simp

/-- Coefficientwise `Y,Z`-contraction of a polynomial pure tensor is a scalar-polynomial
convolution against the `X` polynomial vector. -/
theorem mapLinear_contractX_polynomialPure
    (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (x : ∀ c, PolynomialVector (V c)) :
    PolynomialVector.mapLinear (contractX fy fz) (polynomialPure (K := K) x) =
      PolynomialVector.convolution (LinearMap.lsmul K (V .X))
        (PolynomialVector.convolution (LinearMap.lsmul K K)
          (PolynomialVector.mapLinear fy (x .Y))
          (PolynomialVector.mapLinear fz (x .Z))) (x .X) := by
  rw [← ofLegs_eta x]
  exact mapLinear_contractX_polynomialPure_ofLegs fy fz (x .X) (x .Y) (x .Z)

/-- Explicit three-leg form of `mapLinear_contractY_polynomialPure`. -/
private theorem mapLinear_contractY_polynomialPure_ofLegs
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K)
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) :
    PolynomialVector.mapLinear (contractY fx fz)
        (polynomialPure (K := K) (ofLegs xX xY xZ)) =
      PolynomialVector.convolution (LinearMap.lsmul K (V .Y))
        (PolynomialVector.convolution (LinearMap.lsmul K K)
          (PolynomialVector.mapLinear fx xX) (PolynomialVector.mapLinear fz xZ)) xY := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp [polynomialPure_add_X, map_add, ha, hb,
        PolynomialVector.convolution_add_left]
  | single dx vx =>
      induction xY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp [polynomialPure_add_Y, map_add, ha, hb,
            PolynomialVector.convolution_add_right]
      | single dy vy =>
          induction xZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp [polynomialPure_add_Z, map_add, ha, hb,
                PolynomialVector.convolution_add_left,
                PolynomialVector.convolution_add_right]
          | single dz vz =>
              change PolynomialVector.mapLinear (contractY fx fz)
                  (polynomialPure (K := K) (ofLegs
                    (PolynomialVector.monomial dx vx)
                    (PolynomialVector.monomial dy vy)
                    (PolynomialVector.monomial dz vz))) =
                PolynomialVector.convolution (LinearMap.lsmul K (V .Y))
                  (PolynomialVector.convolution (LinearMap.lsmul K K)
                    (PolynomialVector.mapLinear fx (PolynomialVector.monomial dx vx))
                    (PolynomialVector.mapLinear fz (PolynomialVector.monomial dz vz)))
                  (PolynomialVector.monomial dy vy)
              rw [polynomialPure_monomial, PolynomialVector.mapLinear_monomial,
                PolynomialVector.mapLinear_monomial, PolynomialVector.mapLinear_monomial,
                PolynomialVector.convolution_monomial,
                PolynomialVector.convolution_monomial,
                show dx + dz + dy = dx + dy + dz from by omega]
              simp

/-- Coefficientwise `X,Z`-contraction of a polynomial pure tensor is a scalar-polynomial
convolution against the `Y` polynomial vector. -/
theorem mapLinear_contractY_polynomialPure
    (fx : V .X →ₗ[K] K) (fz : V .Z →ₗ[K] K) (x : ∀ c, PolynomialVector (V c)) :
    PolynomialVector.mapLinear (contractY fx fz) (polynomialPure (K := K) x) =
      PolynomialVector.convolution (LinearMap.lsmul K (V .Y))
        (PolynomialVector.convolution (LinearMap.lsmul K K)
          (PolynomialVector.mapLinear fx (x .X))
          (PolynomialVector.mapLinear fz (x .Z))) (x .Y) := by
  rw [← ofLegs_eta x]
  exact mapLinear_contractY_polynomialPure_ofLegs fx fz (x .X) (x .Y) (x .Z)

/-- Explicit three-leg form of `mapLinear_contractZ_polynomialPure`. -/
private theorem mapLinear_contractZ_polynomialPure_ofLegs
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K)
    (xX : PolynomialVector (V .X)) (xY : PolynomialVector (V .Y))
    (xZ : PolynomialVector (V .Z)) :
    PolynomialVector.mapLinear (contractZ fx fy)
        (polynomialPure (K := K) (ofLegs xX xY xZ)) =
      PolynomialVector.convolution (LinearMap.lsmul K (V .Z))
        (PolynomialVector.convolution (LinearMap.lsmul K K)
          (PolynomialVector.mapLinear fx xX) (PolynomialVector.mapLinear fy xY)) xZ := by
  classical
  induction xX using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp [polynomialPure_add_X, map_add, ha, hb,
        PolynomialVector.convolution_add_left]
  | single dx vx =>
      induction xY using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp [polynomialPure_add_Y, map_add, ha, hb,
            PolynomialVector.convolution_add_left,
            PolynomialVector.convolution_add_right]
      | single dy vy =>
          induction xZ using Finsupp.induction_linear with
          | zero => simp
          | add a b ha hb =>
              simp [polynomialPure_add_Z, map_add, ha, hb,
                PolynomialVector.convolution_add_right]
          | single dz vz =>
              change PolynomialVector.mapLinear (contractZ fx fy)
                  (polynomialPure (K := K) (ofLegs
                    (PolynomialVector.monomial dx vx)
                    (PolynomialVector.monomial dy vy)
                    (PolynomialVector.monomial dz vz))) =
                PolynomialVector.convolution (LinearMap.lsmul K (V .Z))
                  (PolynomialVector.convolution (LinearMap.lsmul K K)
                    (PolynomialVector.mapLinear fx (PolynomialVector.monomial dx vx))
                    (PolynomialVector.mapLinear fy (PolynomialVector.monomial dy vy)))
                  (PolynomialVector.monomial dz vz)
              rw [polynomialPure_monomial, PolynomialVector.mapLinear_monomial,
                PolynomialVector.mapLinear_monomial, PolynomialVector.mapLinear_monomial,
                PolynomialVector.convolution_monomial,
                PolynomialVector.convolution_monomial]
              simp

/-- Coefficientwise `X,Y`-contraction of a polynomial pure tensor is a scalar-polynomial
convolution against the `Z` polynomial vector. -/
theorem mapLinear_contractZ_polynomialPure
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (x : ∀ c, PolynomialVector (V c)) :
    PolynomialVector.mapLinear (contractZ fx fy) (polynomialPure (K := K) x) =
      PolynomialVector.convolution (LinearMap.lsmul K (V .Z))
        (PolynomialVector.convolution (LinearMap.lsmul K K)
          (PolynomialVector.mapLinear fx (x .X))
          (PolynomialVector.mapLinear fy (x .Y))) (x .Z) := by
  rw [← ofLegs_eta x]
  exact mapLinear_contractZ_polynomialPure_ofLegs fx fy (x .X) (x .Y) (x .Z)

/-- Shared degree bookkeeping for the three leg bounds below.  If the two contracted polynomial
vectors are supported in degrees summing to at most `D`, then the doubly convolved scalar
polynomial times `u` lies in the span of the shifts `ε^e • u` with `e ≤ D`.

Proof sketch: coefficients of the convolution beyond the sum of the two degree bounds vanish
(`PolynomialVector.convolution_apply_eq_zero_of_lt`), and applying a linear map coefficientwise
cannot enlarge a support (`PolynomialVector.support_mapLinear_subset`), so the scalar factor is
supported in degrees at most `D`; `PolynomialVector.convolution_lsmul_mem_span_shift`
finishes. -/
private theorem convolution_pair_mem_span_shift
    {M A B : Type*} [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (fa : A →ₗ[K] K) (fb : B →ₗ[K] K)
    (a : PolynomialVector A) (b : PolynomialVector B) (u : PolynomialVector M) {D : ℕ}
    (hD : a.support.sup id + b.support.sup id ≤ D) :
    PolynomialVector.convolution (LinearMap.lsmul K M)
        (PolynomialVector.convolution (LinearMap.lsmul K K)
          (PolynomialVector.mapLinear fa a) (PolynomialVector.mapLinear fb b)) u ∈
      Submodule.span K
        (Set.range fun e : Fin (D + 1) ↦ PolynomialVector.shift (e : ℕ) u) := by
  classical
  refine PolynomialVector.convolution_lsmul_mem_span_shift _ _ ?_
  intro e he
  have ha : ∀ i ∈ (PolynomialVector.mapLinear fa a).support, i ≤ a.support.sup id := fun i hi ↦
    Finset.le_sup (f := id) (PolynomialVector.support_mapLinear_subset _ _ hi)
  have hb : ∀ i ∈ (PolynomialVector.mapLinear fb b).support, i ≤ b.support.sup id := fun i hi ↦
    Finset.le_sup (f := id) (PolynomialVector.support_mapLinear_subset _ _ hi)
  by_contra hgt
  exact Finsupp.mem_support_iff.mp he
    (PolynomialVector.convolution_apply_eq_zero_of_lt _ ha hb
      (lt_of_le_of_lt hD (Nat.lt_of_not_le hgt)))

/-- Generic single-leg assembly: if every coefficientwise contraction of every certificate term
lies in the span of boundedly many shifts of the chosen leg vectors, and the contractions of the
limit tensor span the leg space, then the leg dimension is at most the certificate size. -/
private theorem finrank_le_of_contract_span
    {M : Type*} [AddCommGroup M] [Module K M]
    {ι : Type*} (contract : ι → Tensor3 K V →ₗ[K] M)
    {r d D : ℕ} {T : Tensor3 K V}
    (terms : List (∀ c, PolynomialVector (V c))) (hlen : terms.length ≤ r)
    (hlead : HasLeadingTerm ((terms.map (polynomialPure (K := K))).sum) d T)
    (u : Fin terms.length → PolynomialVector M)
    (hterm : ∀ (q : ι) (j : Fin terms.length),
      PolynomialVector.mapLinear (contract q) (polynomialPure (K := K) (terms.get j)) ∈
        Submodule.span K (Set.range fun e : Fin (D + 1) ↦
          PolynomialVector.shift (e : ℕ) (u j)))
    (hspan : Submodule.span K (Set.range fun q ↦ contract q T) = ⊤) :
    Module.finrank K M ≤ r := by
  classical
  refine le_trans (finrank_le_of_leadingTerm_span_shift
      (A := fun q ↦ PolynomialVector.mapLinear (contract q)
        ((terms.map (polynomialPure (K := K))).sum))
      (v := fun q ↦ contract q T) (d := d) (u := u) (D := D) ?_ ?_ ?_ hspan) hlen
  · intro q e he
    rw [PolynomialVector.mapLinear_apply, hlead.lower_coeff he, map_zero]
  · intro q
    rw [PolynomialVector.mapLinear_apply, hlead.coeff]
  · intro q
    rw [list_map_sum_eq_fin_sum (polynomialPure (K := K)) terms, map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    refine Submodule.span_mono ?_ (hterm q j)
    rintro _ ⟨e, rfl⟩
    exact ⟨(j, e), rfl⟩

/-- Conciseness in `X` makes the dimension of the `X` space a lower bound for border rank.

Proof sketch: a border-rank certificate presents `T` as the degree-`d` leading coefficient of a
sum of at most `r` polynomial pure tensors.  Coefficientwise `Y,Z`-contraction of this path is a
sum of scalar-polynomial convolutions against the fixed `X`-leg polynomial vectors of the
certificate, with degrees bounded by the certificate itself, so all contraction paths lie in the
span of boundedly many shifts of at most `r` generators.  The contractions of `T` are the
degree-`d` coefficients of these paths and span `V .X` by conciseness, so the
leading-coefficient extraction lemma bounds `finrank (V .X)` by `r`. -/
theorem BorderRankLE.finrank_X_le {r : ℕ} {T : Tensor3 K V}
    (hT : BorderRankLE r T) (hconcise : IsConciseX T) :
    Module.finrank K (V .X) ≤ r := by
  classical
  obtain ⟨d, terms, hlen, hlead⟩ := hT
  refine finrank_le_of_contract_span
      (fun q : Module.Dual K (V .Y) × Module.Dual K (V .Z) ↦ contractX q.1 q.2)
      terms hlen hlead (fun j ↦ (terms.get j) .X)
      (D := (terms.map fun x ↦
        (x .Y).support.sup id + (x .Z).support.sup id).sum) ?_ hconcise
  intro q j
  rw [mapLinear_contractX_polynomialPure]
  exact convolution_pair_mem_span_shift q.1 q.2 _ _ _
    (List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem terms j)))

/-- Conciseness in `Y` makes the dimension of the `Y` space a lower bound for border rank. -/
theorem BorderRankLE.finrank_Y_le {r : ℕ} {T : Tensor3 K V}
    (hT : BorderRankLE r T) (hconcise : IsConciseY T) :
    Module.finrank K (V .Y) ≤ r := by
  classical
  obtain ⟨d, terms, hlen, hlead⟩ := hT
  refine finrank_le_of_contract_span
      (fun q : Module.Dual K (V .X) × Module.Dual K (V .Z) ↦ contractY q.1 q.2)
      terms hlen hlead (fun j ↦ (terms.get j) .Y)
      (D := (terms.map fun x ↦
        (x .X).support.sup id + (x .Z).support.sup id).sum) ?_ hconcise
  intro q j
  rw [mapLinear_contractY_polynomialPure]
  exact convolution_pair_mem_span_shift q.1 q.2 _ _ _
    (List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem terms j)))

/-- Conciseness in `Z` makes the dimension of the `Z` space a lower bound for border rank. -/
theorem BorderRankLE.finrank_Z_le {r : ℕ} {T : Tensor3 K V}
    (hT : BorderRankLE r T) (hconcise : IsConciseZ T) :
    Module.finrank K (V .Z) ≤ r := by
  classical
  obtain ⟨d, terms, hlen, hlead⟩ := hT
  refine finrank_le_of_contract_span
      (fun q : Module.Dual K (V .X) × Module.Dual K (V .Y) ↦ contractZ q.1 q.2)
      terms hlen hlead (fun j ↦ (terms.get j) .Z)
      (D := (terms.map fun x ↦
        (x .X).support.sup id + (x .Y).support.sup id).sum) ?_ hconcise
  intro q j
  rw [mapLinear_contractZ_polynomialPure]
  exact convolution_pair_mem_span_shift q.1 q.2 _ _ _
    (List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem terms j)))

/-- The border rank of a concise tensor is at least the largest of its three leg dimensions. -/
theorem BorderRankLE.max_finrank_le {r : ℕ} {T : Tensor3 K V}
    (hT : BorderRankLE r T) (hconcise : IsConcise T) :
    max (Module.finrank K (V .X))
        (max (Module.finrank K (V .Y)) (Module.finrank K (V .Z))) ≤ r := by
  rw [max_le_iff, max_le_iff]
  exact ⟨hT.finrank_X_le hconcise.1,
    hT.finrank_Y_le hconcise.2.1, hT.finrank_Z_le hconcise.2.2⟩

/-- Degree-aware version: a size-`r` border-rank certificate at any leading degree for an
`X`-concise tensor forces `finrank (V .X) ≤ r`. -/
theorem BorderRankLEAt.finrank_X_le {r d : ℕ} {T : Tensor3 K V}
    (hT : BorderRankLEAt r d T) (hconcise : IsConciseX T) :
    Module.finrank K (V .X) ≤ r :=
  hT.toBorderRankLE.finrank_X_le hconcise

/-- Degree-aware version of the `Y`-leg border-rank conciseness bound. -/
theorem BorderRankLEAt.finrank_Y_le {r d : ℕ} {T : Tensor3 K V}
    (hT : BorderRankLEAt r d T) (hconcise : IsConciseY T) :
    Module.finrank K (V .Y) ≤ r :=
  hT.toBorderRankLE.finrank_Y_le hconcise

/-- Degree-aware version of the `Z`-leg border-rank conciseness bound. -/
theorem BorderRankLEAt.finrank_Z_le {r d : ℕ} {T : Tensor3 K V}
    (hT : BorderRankLEAt r d T) (hconcise : IsConciseZ T) :
    Module.finrank K (V .Z) ≤ r :=
  hT.toBorderRankLE.finrank_Z_le hconcise

/-- Degree-aware version of the maximum-dimension border-rank lower bound. -/
theorem BorderRankLEAt.max_finrank_le {r d : ℕ} {T : Tensor3 K V}
    (hT : BorderRankLEAt r d T) (hconcise : IsConcise T) :
    max (Module.finrank K (V .X))
        (max (Module.finrank K (V .Y)) (Module.finrank K (V .Z))) ≤ r :=
  hT.toBorderRankLE.max_finrank_le hconcise

/-- Numeric form: the `X` dimension of an `X`-concise tensor bounds its border rank from below. -/
theorem finrank_X_le_borderRank {T : Tensor3 K V} (hconcise : IsConciseX T) :
    Module.finrank K (V .X) ≤ borderRank T :=
  (borderRank_spec T).finrank_X_le hconcise

/-- Numeric form: the `Y` dimension of a `Y`-concise tensor bounds its border rank from below. -/
theorem finrank_Y_le_borderRank {T : Tensor3 K V} (hconcise : IsConciseY T) :
    Module.finrank K (V .Y) ≤ borderRank T :=
  (borderRank_spec T).finrank_Y_le hconcise

/-- Numeric form: the `Z` dimension of a `Z`-concise tensor bounds its border rank from below. -/
theorem finrank_Z_le_borderRank {T : Tensor3 K V} (hconcise : IsConciseZ T) :
    Module.finrank K (V .Z) ≤ borderRank T :=
  (borderRank_spec T).finrank_Z_le hconcise

/-- Numeric form: the border rank of a concise tensor is at least its largest leg dimension. -/
theorem max_finrank_le_borderRank {T : Tensor3 K V} (hconcise : IsConcise T) :
    max (Module.finrank K (V .X))
        (max (Module.finrank K (V .Y)) (Module.finrank K (V .Z))) ≤ borderRank T :=
  (borderRank_spec T).max_finrank_le hconcise

end BorderConciseness

end AlgebraicComplexity.Tensor
