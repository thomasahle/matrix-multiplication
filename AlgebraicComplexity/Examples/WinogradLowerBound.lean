/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.Strassen
import AlgebraicComplexity.Tensor.Concise
import AlgebraicComplexity.Tensor.SubstitutionMethod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Winograd's lower bound: `2 × 2` matrix multiplication has rank seven

This client proves, over an arbitrary field `K`, that every constructive rank certificate for the
`2 × 2` matrix-multiplication tensor `⟨2,2,2⟩` has length at least `7`, and combines this with
Strassen's rank-seven certificate to conclude `rank ⟨2,2,2⟩ = 7`.

The lower bound is due to Winograd [*On multiplication of 2×2 matrices*, Linear Algebra Appl. 4
(1971), 381–388] and, over `𝔽₂`, Hopcroft–Kerr [*On minimizing the number of multiplications
necessary for matrix multiplication*, SIAM J. Appl. Math. 20 (1971), 30–36].  The argument
formalized here follows the substitution-method proof of Bläser, Christandl, and Zuiddam
[*The border support rank of two-by-two matrix multiplication is seven*, Chicago J. Theor.
Comput. Sci. 2018, Article 05, second proof of Theorem 1.1], specialized from support rank to
ordinary rank and reorganized so that every variable substitution is a single adaptive step.

## Route

This file is a second, independent route to the bound ("Route B"): it deliberately does not use
the tensor-level substitution machinery of `Tensor/SubstitutionMethod.lean`.  Instead it works
with the trilinear-form evaluation of a rank certificate.  The one thing the two routes do share
is the projection itself — `Winograd.subProj` is `Tensor.substProj` against a normalized
covector — which is a statement about a single module and carries no tensor structure.

* A rank certificate of length `r` for `⟨2,2,2⟩` is converted, through the dual contractions of
  `Tensor/Concise.lean`, into a list of `r` triples of linear forms `(u, v, w)` on the space of
  `2 × 2` matrices satisfying `∑ u(A)·v(B)·w(C) = trace (A*B*C)` for all matrices `A`, `B`, `C`
  (`Winograd.Computes`, `Winograd.computes_of_rankLE`).
* `Winograd.Computes.length_ge_seven` shows that any such list has length at least `7`:
  1. a *sandwich* normalization `(A,B,C) ↦ (P'*A, B*R', R*C*P)`, which fixes the target
     `trace (A*B*C)`, arranges that some `w`-form satisfies `w(E₀₀) = 0` and `w(E₁₀) = 1`
     (`exists_sandwich_normalizer`);
  2. five substitution steps follow, each replacing one matrix variable by a linear combination
     of the other variables via the projection `X ↦ X - c⁻¹·f(X) • E`; each step removes one
     term from the decomposition, and the term to remove is *found adaptively* by evaluating the
     current trilinear identity at an explicit triple of matrix units, where the accumulated
     substitution corrections vanish structurally (the parametrized trace computations
     `trace_T2`–`trace_T5`);
  3. after killing one `w`-form, two `v`-forms and two `u`-forms, at most `r - 5` terms remain,
     while the remaining identity still computes the two independent slices `A ↦ A 0 0` and
     `A ↦ A 0 1` (`trace_sliceA`, `trace_sliceB`); a list of length at most one cannot compute
     two independent linear forms, so `r ≥ 7`.
* The bridge back to tensors gives `matrixMultiplication_two_rank_lower_seven`,
  `seven_le_rank_matrixMultiplication_two`, and, together with Strassen's certificate,
  `rank_matrixMultiplication_two : rank ⟨2,2,2⟩ = 7`.

## Shared candidate lemma

`exists_isUnit_sum_entry_mul_eq_zero` is the invertible-hyperplane lemma: the kernel of the
entrywise pairing against any coefficient matrix `B` on `2 × 2` matrices contains an invertible
matrix, over every field, by a fully constructive case analysis on the entries of `B` (for
nonzero `B` this kernel is a genuine hyperplane).

It currently has **no consumer**, here or anywhere else in the repository: Route B's main chain
uses the sandwich normalization `exists_sandwich_normalizer` in the analogous role, and Route A
(`Examples/BlaeserLowerBound.lean`) goes through the uniform chain interface of
`Tensor/SubstitutionMethodScale.lean`, which needs no invertible witness at all.  It is kept
because it is the shape of hypothesis that an Alder–Strassen or Bläser-style argument would
need — those normalize a detecting covector by an invertible sandwich — and because it is the
one genuinely reusable, dimension-free fact this file proves.  It is asserted by name in
`AxiomAudit.lean`; its unqualified top-level name is a wart that should be fixed in a session
permitted to edit that audit.

## Three independent routes to `rank ⟨2,2,2⟩`

Three methodologically distinct arguments about `⟨2,2,2⟩` live in the repository:

1. *substitution / row-kill* — `Examples/BlaeserLowerBound.lean` reaches `6`
   (`rank_matrixMultiplication_rowKill`); the `5` and `6` of
   `Examples/SmallMatrixLowerBounds.lean` are its one- and two-kill specializations, not a
   separate argument;
2. *Koszul flattening* — `MatrixMultiplication/KoszulBorderRank.lean` reaches `6` again, but as a
   *border*-rank bound, from the rank of an explicit `12 × 8` matrix;
3. *trilinear substitution with sandwich normalization* — this file, the only route that reaches
   the exact value `7`.

The step that separates route 3 from route 1 is precisely the one route 1 cannot take: after five
substitutions the surviving flattening depends on the substitution directions, so the argument
needs an adaptive normalization (`exists_sandwich_normalizer`) rather than a protected coordinate
row.

## Non-goals

This file proves nothing about border rank or support rank, and it does not attempt general
`⟨m,n,p⟩` substitution bounds.  Only leaf results about `⟨2,2,2⟩` are stated.
-/

namespace AlgebraicComplexity

open Tensor

universe u

namespace Winograd

variable {K : Type u} [Field K]

/-! ### Matrix units and elementary matrix computations -/

/-- The `2 × 2` matrix unit with a one in row 0, column 0. -/
private def E00 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, 0]

/-- The `2 × 2` matrix unit with a one in row 0, column 1. -/
private def E01 : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

/-- The `2 × 2` matrix unit with a one in row 1, column 0. -/
private def E10 : Matrix (Fin 2) (Fin 2) K := !![0, 0; 1, 0]

/-- The `2 × 2` matrix unit with a one in row 1, column 1. -/
private def E11 : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, 1]

/-- Every `2 × 2` matrix is the combination of the four matrix units weighted by its entries. -/
private theorem matrix_eq_sum_units (M : Matrix (Fin 2) (Fin 2) K) :
    M = M 0 0 • E00 + M 0 1 • E01 + M 1 0 • E10 + M 1 1 • E11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E00, E01, E10, E11]

/-- A linear form on `2 × 2` matrices is determined by its four values on the matrix units. -/
private theorem form_apply_eq (w : Matrix (Fin 2) (Fin 2) K →ₗ[K] K)
    (M : Matrix (Fin 2) (Fin 2) K) :
    w M = M 0 0 * w E00 + M 0 1 * w E01 + M 1 0 * w E10 + M 1 1 * w E11 := by
  conv_lhs => rw [matrix_eq_sum_units M]
  simp [smul_eq_mul]

/-! ### Trilinear-form decompositions -/

/-- One term of a trilinear decomposition: a triple of linear forms on `2 × 2` matrices.  The
term evaluates on a matrix triple `(A, B, C)` to the product `u A * v B * w C`. -/
structure Triple (K : Type u) [Field K] where
  /-- The linear form applied to the first argument. -/
  u : Matrix (Fin 2) (Fin 2) K →ₗ[K] K
  /-- The linear form applied to the second argument. -/
  v : Matrix (Fin 2) (Fin 2) K →ₗ[K] K
  /-- The linear form applied to the third argument. -/
  w : Matrix (Fin 2) (Fin 2) K →ₗ[K] K

/-- The list `L` of rank-one trilinear terms computes the trilinear form `F`: for all matrix
arguments, the sum of the term products equals the value of `F`. -/
def Computes (F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K →
    Matrix (Fin 2) (Fin 2) K → K) (L : List (Triple K)) : Prop :=
  ∀ A B C, (L.map fun t => t.u A * t.v B * t.w C).sum = F A B C

/-- The trace trilinear form `(A, B, C) ↦ trace (A * B * C)` of `2 × 2` matrix
multiplication. -/
def mulTrace (K : Type u) [Field K] :
    Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → K :=
  fun A B C => (A * B * C).trace

/-- If a decomposition computes `F` and `F` is nonzero at a point, then some term of the
decomposition has all three factors nonzero at that point. -/
private theorem exists_triple_of_ne_zero
    {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → K}
    {L : List (Triple K)} (h : Computes F L) {X Y Z : Matrix (Fin 2) (Fin 2) K}
    (hF : F X Y Z ≠ 0) :
    ∃ t ∈ L, t.u X ≠ 0 ∧ t.v Y ≠ 0 ∧ t.w Z ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hF
  rw [← h X Y Z]
  apply List.sum_eq_zero
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  by_cases hu : t.u X = 0
  · simp [hu]
  by_cases hv : t.v Y = 0
  · simp [hv]
  have hw := hall t ht hu hv
  simp [hw]

/-! ### The substitution step

Each substitution replaces one matrix variable of the trilinear identity by a linear combination
of the other variables.  Formally the variable matrix is mapped through the projection
`X ↦ X - c⁻¹ * f X • E` onto the kernel of a detecting form `f`, where `E` is the matrix unit of
the substituted position and `c = f E ≠ 0`.  Applying this projection to one argument of a
decomposition annihilates every term whose corresponding form is proportional to `f`, in
particular the chosen term, so the surviving decomposition is strictly shorter.  This is the
classical substitution method of Winograd and Hopcroft–Kerr, implemented directly on trilinear
forms. -/

/-- The bundled substitution projection `X ↦ X - (f E)⁻¹ * f X • E`: the module-level
`Tensor.substProj` of `Tensor/SubstitutionMethod.lean` against the covector `f` normalized so
that it takes the value one at `E`. -/
private def subProj (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] K) (E : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  Tensor.substProj ((f E)⁻¹ • f) E

/-- Evaluation formula for the substitution projection. -/
private theorem subProj_apply (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] K)
    (E X : Matrix (Fin 2) (Fin 2) K) :
    subProj f E X = X - ((f E)⁻¹ * f X) • E := by
  simp [subProj, smul_eq_mul]

/-- The substitution projection annihilates its detecting form. -/
private theorem apply_subProj (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] K)
    {E : Matrix (Fin 2) (Fin 2) K} (hE : f E ≠ 0) (X : Matrix (Fin 2) (Fin 2) K) :
    f (subProj f E X) = 0 := by
  have hnorm : ((f E)⁻¹ • f) E = 1 := by
    simp [smul_eq_mul, inv_mul_cancel₀ hE]
  have h := Tensor.phi_substProj_apply hnorm X
  rw [LinearMap.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hE)

/-- Substitution step in the third argument: a term whose `w`-form is nonzero at the matrix `E`
can be killed, shortening the decomposition by one at the price of projecting the third
argument of the computed trilinear form.

`killV` and `killU` below are deliberate mirrors: the three proofs are identical modulo which
field of `Triple` is projected.  Collapsing them would need a `Triple.rotate` together with
`Computes.rotate : Computes F L → Computes (fun A B C ↦ F C A B) (L.map Triple.rotate)`, and the
rotated shape of `F` makes the five call sites in `Computes.length_ge_seven` markedly harder to
read than the explicit forms; the triplication is kept on purpose. -/
private theorem killW
    {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → K}
    {L : List (Triple K)} (h : Computes F L) {t₀ : Triple K} (ht₀ : t₀ ∈ L)
    {E : Matrix (Fin 2) (Fin 2) K} (hE : t₀.w E ≠ 0) :
    ∃ L' : List (Triple K), L'.length + 1 = L.length ∧
      Computes (fun A B C => F A B (C - ((t₀.w E)⁻¹ * t₀.w C) • E)) L' := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ht₀
  refine ⟨(s ++ t).map fun t' => ⟨t'.u, t'.v, t'.w ∘ₗ subProj t₀.w E⟩,
    by simp only [List.length_map, List.length_append, List.length_cons]; omega, ?_⟩
  intro A B C
  have hsub := h A B (subProj t₀.w E C)
  have hkill : t₀.w (subProj t₀.w E C) = 0 := apply_subProj t₀.w hE C
  rw [subProj_apply] at hsub hkill
  show _ = F A B (C - ((t₀.w E)⁻¹ * t₀.w C) • E)
  rw [← hsub]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, List.map_map]
  rw [hkill, mul_zero, zero_add]
  congr 1

/-- Substitution step in the second argument; see `killW`. -/
private theorem killV
    {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → K}
    {L : List (Triple K)} (h : Computes F L) {t₀ : Triple K} (ht₀ : t₀ ∈ L)
    {E : Matrix (Fin 2) (Fin 2) K} (hE : t₀.v E ≠ 0) :
    ∃ L' : List (Triple K), L'.length + 1 = L.length ∧
      Computes (fun A B C => F A (B - ((t₀.v E)⁻¹ * t₀.v B) • E) C) L' := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ht₀
  refine ⟨(s ++ t).map fun t' => ⟨t'.u, t'.v ∘ₗ subProj t₀.v E, t'.w⟩,
    by simp only [List.length_map, List.length_append, List.length_cons]; omega, ?_⟩
  intro A B C
  have hsub := h A (subProj t₀.v E B) C
  have hkill : t₀.v (subProj t₀.v E B) = 0 := apply_subProj t₀.v hE B
  rw [subProj_apply] at hsub hkill
  show _ = F A (B - ((t₀.v E)⁻¹ * t₀.v B) • E) C
  rw [← hsub]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, List.map_map]
  rw [hkill, mul_zero, zero_mul, zero_add]
  congr 1

/-- Substitution step in the first argument; see `killW`. -/
private theorem killU
    {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K → K}
    {L : List (Triple K)} (h : Computes F L) {t₀ : Triple K} (ht₀ : t₀ ∈ L)
    {E : Matrix (Fin 2) (Fin 2) K} (hE : t₀.u E ≠ 0) :
    ∃ L' : List (Triple K), L'.length + 1 = L.length ∧
      Computes (fun A B C => F (A - ((t₀.u E)⁻¹ * t₀.u A) • E) B C) L' := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ht₀
  refine ⟨(s ++ t).map fun t' => ⟨t'.u ∘ₗ subProj t₀.u E, t'.v, t'.w⟩,
    by simp only [List.length_map, List.length_append, List.length_cons]; omega, ?_⟩
  intro A B C
  have hsub := h (subProj t₀.u E A) B C
  have hkill : t₀.u (subProj t₀.u E A) = 0 := apply_subProj t₀.u hE A
  rw [subProj_apply] at hsub hkill
  show _ = F (A - ((t₀.u E)⁻¹ * t₀.u A) • E) B C
  rw [← hsub]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, List.map_map]
  rw [hkill, zero_mul, zero_mul, zero_add]
  congr 1

/-! ### The sandwich normalization

The trace form is invariant under `(A, B, C) ↦ (P' * A, B * R', R * C * P)` whenever `P'` and
`R'` are two-sided inverses of `P` and `R`: the three matrix products telescope into a
conjugation inside the trace.  This transports any decomposition to a decomposition of the same
length whose `w`-forms are precomposed with `C ↦ R * C * P`.  Choosing `R` and `P` adapted to
one fixed nonzero `w`-form realizes the normalization `w (E₀₀) = 0`, `w (E₁₀) = 1` that starts
the substitution chain. -/

/-- Left multiplication by a fixed matrix, as a linear map. -/
private def mulLeftLM (G : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun A := G * A
  map_add' A B := Matrix.mul_add G A B
  map_smul' s A := by simp

@[local simp] private theorem mulLeftLM_apply (G A : Matrix (Fin 2) (Fin 2) K) :
    mulLeftLM G A = G * A := rfl

/-- Right multiplication by a fixed matrix, as a linear map. -/
private def mulRightLM (G : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun A := A * G
  map_add' A B := Matrix.add_mul A B G
  map_smul' s A := by simp

@[local simp] private theorem mulRightLM_apply (G A : Matrix (Fin 2) (Fin 2) K) :
    mulRightLM G A = A * G := rfl

/-- Two-sided multiplication `C ↦ R * C * P`, as a linear map. -/
private def sandwichLM (R P : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun C := R * C * P
  map_add' C D := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' s C := by simp

@[local simp] private theorem sandwichLM_apply (R P C : Matrix (Fin 2) (Fin 2) K) :
    sandwichLM R P C = R * C * P := rfl

/-- Sandwiching a decomposition of the trace form by two inverse pairs yields another
decomposition of the trace form of the same length.

Proof sketch: instantiating the given decomposition at `(P' * A, B * R', R * C * P)` makes the
matrix products telescope, `P' * A * (B * R') * (R * C * P) = P' * (A * B * C) * P`, and the
trace of the conjugated product equals the trace of `A * B * C` by cyclicity. -/
private theorem computes_sandwich {L : List (Triple K)} (h : Computes (mulTrace K) L)
    {P P' R R' : Matrix (Fin 2) (Fin 2) K}
    (hPP' : P * P' = 1) (hR'R : R' * R = 1) :
    Computes (mulTrace K)
      (L.map fun t => ⟨t.u ∘ₗ mulLeftLM P', t.v ∘ₗ mulRightLM R', t.w ∘ₗ sandwichLM R P⟩) := by
  intro A B C
  have hval := h (P' * A) (B * R') (R * C * P)
  rw [List.map_map]
  have hmap : ((fun t : Triple K => t.u A * t.v B * t.w C) ∘
      fun t : Triple K => Triple.mk (t.u ∘ₗ mulLeftLM P') (t.v ∘ₗ mulRightLM R')
        (t.w ∘ₗ sandwichLM R P)) =
      fun t : Triple K => t.u (P' * A) * t.v (B * R') * t.w (R * C * P) := by
    funext t
    simp
  rw [hmap, hval]
  unfold mulTrace
  have hprod : P' * A * (B * R') * (R * C * P) = P' * (A * B * C) * P := by
    calc P' * A * (B * R') * (R * C * P)
        = P' * A * (B * (R' * R) * C * P) := by
          simp only [Matrix.mul_assoc]
      _ = P' * (A * B * C) * P := by
          rw [hR'R, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [hprod]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]

/-- Constructive normal form for a nonzero pair: an explicit determinant-one matrix `R`, with
explicit inverse, whose first column is annihilated by the covector `(φ₀, φ₁)` while the second
column takes the value one. -/
private theorem exists_column_normalizer (φ₀ φ₁ : K) (hφ : φ₀ ≠ 0 ∨ φ₁ ≠ 0) :
    ∃ R R' : Matrix (Fin 2) (Fin 2) K, R * R' = 1 ∧ R' * R = 1 ∧
      φ₀ * R 0 0 + φ₁ * R 1 0 = 0 ∧ φ₀ * R 0 1 + φ₁ * R 1 1 = 1 := by
  by_cases h0 : φ₀ = 0
  · have h1 : φ₁ ≠ 0 := by
      rcases hφ with h | h
      · exact absurd h0 h
      · exact h
    refine ⟨!![φ₁, 0; 0, φ₁⁻¹], !![φ₁⁻¹, 0; 0, φ₁], ?_, ?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ h1, inv_mul_cancel₀ h1]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ h1, inv_mul_cancel₀ h1]
    · simp [h0]
    · simp [h0, h1]
  · refine ⟨!![φ₁, φ₀⁻¹; -φ₀, 0], !![0, -φ₀⁻¹; φ₀, φ₁], ?_, ?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        · try simp [Matrix.mul_apply, Fin.sum_univ_two]
          try field_simp
          try ring
    · ext i j
      fin_cases i <;> fin_cases j <;>
        · try simp [Matrix.mul_apply, Fin.sum_univ_two]
          try field_simp
          try ring
    · simp
      ring
    · simp [h0]

/-- The value of a form on `R * E₀₀ * P` and `R * E₁₀ * P` depends only on the first row of `P`
and the values of the form on the corresponding column of matrix units; explicit version for
`P = 1` (first row `(1,0)`, selecting column 0). -/
private theorem sandwich_value_col0 (w : Matrix (Fin 2) (Fin 2) K →ₗ[K] K)
    (R : Matrix (Fin 2) (Fin 2) K) :
    w (R * E00 * 1) = R 0 0 * w E00 + R 1 0 * w E10 ∧
      w (R * E10 * 1) = R 0 1 * w E00 + R 1 1 * w E10 := by
  have h1 : R * E00 * 1 = R 0 0 • E00 + R 1 0 • E10 := by
    rw [Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E00, E10, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : R * E10 * 1 = R 0 1 • E00 + R 1 1 • E10 := by
    rw [Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E00, E10, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · rw [h1]; simp [smul_eq_mul]
  · rw [h2]; simp [smul_eq_mul]

/-- Explicit version of the sandwich values for `P` the swap matrix (first row `(0,1)`,
selecting column 1). -/
private theorem sandwich_value_col1 (w : Matrix (Fin 2) (Fin 2) K →ₗ[K] K)
    (R : Matrix (Fin 2) (Fin 2) K) :
    w (R * E00 * !![0, 1; 1, 0]) = R 0 0 * w E01 + R 1 0 * w E11 ∧
      w (R * E10 * !![0, 1; 1, 0]) = R 0 1 * w E01 + R 1 1 * w E11 := by
  have h1 : R * E00 * !![0, 1; 1, 0] = R 0 0 • E01 + R 1 0 • E11 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E00, E01, E11, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : R * E10 * !![0, 1; 1, 0] = R 0 1 • E01 + R 1 1 • E11 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E10, E01, E11, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · rw [h1]; simp [smul_eq_mul]
  · rw [h2]; simp [smul_eq_mul]

/-- For every nonzero linear form `w` on `2 × 2` matrices there are two invertible sandwich
matrices `R`, `P`, with explicit two-sided inverses, such that the transported form
`C ↦ w (R * C * P)` vanishes on the matrix unit `E₀₀` and takes the value one on `E₁₀`.

Proof sketch: some matrix unit detects `w`.  The products `R * E₀₀ * P` and `R * E₁₀ * P` are
combinations of the units in the column selected by the first row of `P`, weighted by the
columns of `R`.  Choose `P` to select a column `j` on which `w` does not vanish identically and
choose `R` by `exists_column_normalizer` for the value pair of `w` on column `j`. -/
private theorem exists_sandwich_normalizer (w : Matrix (Fin 2) (Fin 2) K →ₗ[K] K)
    (hw : w ≠ 0) :
    ∃ R R' P P' : Matrix (Fin 2) (Fin 2) K,
      R * R' = 1 ∧ R' * R = 1 ∧ P * P' = 1 ∧ P' * P = 1 ∧
      w (R * E00 * P) = 0 ∧ w (R * E10 * P) = 1 := by
  have hunit : ¬(w (E00 (K := K)) = 0 ∧ w (E01 (K := K)) = 0 ∧
      w (E10 (K := K)) = 0 ∧ w (E11 (K := K)) = 0) := by
    rintro ⟨h1, h2, h3, h4⟩
    apply hw
    ext M
    rw [form_apply_eq, h1, h2, h3, h4]
    simp
  by_cases hcol0 : w (E00 (K := K)) ≠ 0 ∨ w (E10 (K := K)) ≠ 0
  · obtain ⟨R, R', hRR', hR'R, hker, hone⟩ :=
      exists_column_normalizer (w E00) (w E10) hcol0
    refine ⟨R, R', 1, 1, hRR', hR'R, Matrix.one_mul 1, Matrix.one_mul 1, ?_, ?_⟩
    · rw [(sandwich_value_col0 w R).1]
      calc R 0 0 * w E00 + R 1 0 * w E10
          = w E00 * R 0 0 + w E10 * R 1 0 := by ring
        _ = 0 := hker
    · rw [(sandwich_value_col0 w R).2]
      calc R 0 1 * w E00 + R 1 1 * w E10
          = w E00 * R 0 1 + w E10 * R 1 1 := by ring
        _ = 1 := hone
  · push Not at hcol0
    have hcol1 : w (E01 (K := K)) ≠ 0 ∨ w (E11 (K := K)) ≠ 0 := by
      by_contra hboth
      push Not at hboth
      exact hunit ⟨hcol0.1, hboth.1, hcol0.2, hboth.2⟩
    obtain ⟨R, R', hRR', hR'R, hker, hone⟩ :=
      exists_column_normalizer (w E01) (w E11) hcol1
    have hswap : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 1, 0] = 1 := by
      rw [Matrix.mul_fin_two, Matrix.one_fin_two]
      norm_num
    refine ⟨R, R', !![0, 1; 1, 0], !![0, 1; 1, 0], hRR', hR'R, hswap, hswap, ?_, ?_⟩
    · rw [(sandwich_value_col1 w R).1]
      calc R 0 0 * w E01 + R 1 0 * w E11
          = w E01 * R 0 0 + w E11 * R 1 0 := by ring
        _ = 0 := hker
    · rw [(sandwich_value_col1 w R).2]
      calc R 0 1 * w E01 + R 1 1 * w E11
          = w E01 * R 0 1 + w E11 * R 1 1 := by ring
        _ = 1 := hone

/-! ### The explicit trace computations

Each substitution step is justified by evaluating the current trilinear identity at a triple of
matrix units.  The accumulated substitutions contribute corrections along fixed matrix units
whose products vanish structurally, so every test value is exactly `1` and the two final slices
are exactly the matrix entries `A 0 0` and `A 0 1`, independently of all substitution
parameters.  The parameters `s, a, b, b', k, g, g', p, q` below are those correction
coefficients. -/

/-- Test value for the first `v`-kill: the trace identity at `(E₁₁, E₁₁, E₁₁)` after the
`w`-substitution along `E₁₀`. -/
private theorem trace_T2 (s : K) : mulTrace K E11 E11 (E11 - s • E10) = 1 := by
  unfold mulTrace
  simp [E10, E11, Matrix.trace_fin_two]

/-- Test value for the second `v`-kill, at `(E₁₀, E₀₁, E₁₁)`. -/
private theorem trace_T3 (a s : K) :
    mulTrace K E10 (E01 - a • E11) (E11 - s • E10) = 1 := by
  unfold mulTrace
  simp [E01, E10, E11, Matrix.trace_fin_two]

/-- Test value for the first `u`-kill, at `(E₁₀, E₀₀, E₀₁)`. -/
private theorem trace_T4 (b b' s : K) :
    mulTrace K E10 ((E00 - b • E01) - b' • E11) (E01 - s • E10) = 1 := by
  unfold mulTrace
  simp [E00, E01, E10, E11, Matrix.trace_fin_two]

/-- Test value for the second `u`-kill, at `(E₁₁, E₁₀, E₀₁)`. -/
private theorem trace_T5 (k g g' s : K) :
    mulTrace K (E11 - k • E10) ((E10 - g • E01) - g' • E11) (E01 - s • E10) = 1 := by
  unfold mulTrace
  simp [E01, E10, E11, Matrix.trace_fin_two]

/-- First final slice: after all five substitutions the identity at `(A, E₀₀, E₀₀)` computes the
matrix entry `A 0 0`. -/
private theorem trace_sliceA (A : Matrix (Fin 2) (Fin 2) K) (q p b b' : K) :
    mulTrace K ((A - q • E11) - p • E10) ((E00 - b • E01) - b' • E11) E00 = A 0 0 := by
  unfold mulTrace
  simp [E00, E01, E10, E11, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- Second final slice: after all five substitutions the identity at `(A, E₁₀, E₀₀)` computes
the matrix entry `A 0 1`. -/
private theorem trace_sliceB (A : Matrix (Fin 2) (Fin 2) K) (q p g g' : K) :
    mulTrace K ((A - q • E11) - p • E10) ((E10 - g • E01) - g' • E11) E00 = A 0 1 := by
  unfold mulTrace
  simp [E00, E01, E10, E11, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The initial detection value: the trace identity at `(E₀₀, E₀₀, E₀₀)` equals one. -/
private theorem trace_T0 : mulTrace K E00 E00 E00 = 1 := by
  unfold mulTrace
  simp [E00, Matrix.trace_fin_two]

/-! ### The main lower bound for trilinear decompositions -/

/-- **Winograd's lower bound, trilinear form.**  Every decomposition of the `2 × 2` matrix
trace form `(A, B, C) ↦ trace (A * B * C)` into rank-one products of linear forms has at least
seven terms, over every field.

Proof sketch: this is the substitution-method proof of Bläser–Christandl–Zuiddam (2018),
specialized to the exact tensor and sequentialized.  First a term with nonzero `w`-form is
sandwich-normalized so that its `w`-form vanishes on `E₀₀` and equals one on `E₁₀`
(`exists_sandwich_normalizer`; this uses the invariance of the trace form under
`(A,B,C) ↦ (P'A, BR', RCP)`).  Killing that term substitutes the `C`-variable along `E₁₀`.
Four further adaptive kills follow: `v`-forms at `E₁₁` and `E₀₁`, then `u`-forms at `E₁₀` and
`E₁₁`; each detecting term exists because the current identity evaluates to `1` at an explicit
triple of matrix units (`trace_T2`–`trace_T5`), uniformly in all substitution parameters.  At
most `length - 5` terms remain, but the surviving identity computes both slices `A ↦ A 0 0` and
`A ↦ A 0 1` (`trace_sliceA`, `trace_sliceB`; here the normalization `w(E₀₀) = 0` enters), and a
list of at most one rank-one term cannot compute two linearly independent forms.  Hence
`length ≥ 7`. -/
theorem Computes.length_ge_seven {L : List (Triple K)} (h : Computes (mulTrace K) L) :
    7 ≤ L.length := by
  by_contra hlt
  push Not at hlt
  -- Step 0: find a term with a nonzero `w`-form.
  obtain ⟨t₀, ht₀, -, -, hw₀⟩ :=
    exists_triple_of_ne_zero h (X := E00) (Y := E00) (Z := E00)
      (by rw [trace_T0]; exact one_ne_zero)
  have hwform : t₀.w ≠ 0 := by
    intro h0
    rw [h0] at hw₀
    exact hw₀ rfl
  -- Step 0': sandwich-normalize that term.
  obtain ⟨R, R', P, P', hRR', hR'R, hPP', hP'P, hn0, hn1⟩ :=
    exists_sandwich_normalizer t₀.w hwform
  have h₁ := computes_sandwich h hPP' hR'R
  set t₁ : Triple K :=
    ⟨t₀.u ∘ₗ mulLeftLM P', t₀.v ∘ₗ mulRightLM R', t₀.w ∘ₗ sandwichLM R P⟩ with ht₁def
  have ht₁ : t₁ ∈ L.map fun t : Triple K =>
      (⟨t.u ∘ₗ mulLeftLM P', t.v ∘ₗ mulRightLM R', t.w ∘ₗ sandwichLM R P⟩ : Triple K) :=
    List.mem_map_of_mem ht₀
  have hw100 : t₁.w E00 = 0 := by
    rw [ht₁def]
    simpa using hn0
  have hw110 : t₁.w E10 = 1 := by
    rw [ht₁def]
    simpa using hn1
  -- Kill 1: the normalized `w`-form, substituting `C` along `E₁₀`.
  obtain ⟨L₂, hlen₂, h₂⟩ := killW h₁ ht₁ (E := E10) (by rw [hw110]; exact one_ne_zero)
  simp only [hw110, inv_one, one_mul] at h₂
  -- Kill 2: a `v`-form detected at `E₁₁`, substituting `B` along `E₁₁`.
  obtain ⟨t₂, ht₂, -, hv₂, -⟩ :=
    exists_triple_of_ne_zero h₂ (X := E11) (Y := E11) (Z := E11)
      (by
        show mulTrace K E11 E11 (E11 - t₁.w E11 • E10) ≠ 0
        rw [trace_T2]; exact one_ne_zero)
  obtain ⟨L₃, hlen₃, h₃⟩ := killV h₂ ht₂ (E := E11) hv₂
  -- Kill 3: a `v`-form detected at `E₀₁`, substituting `B` along `E₀₁`.
  obtain ⟨t₃, ht₃, -, hv₃, -⟩ :=
    exists_triple_of_ne_zero h₃ (X := E10) (Y := E01) (Z := E11)
      (by
        show mulTrace K E10 (E01 - ((t₂.v E11)⁻¹ * t₂.v E01) • E11)
          (E11 - t₁.w E11 • E10) ≠ 0
        rw [trace_T3]; exact one_ne_zero)
  obtain ⟨L₄, hlen₄, h₄⟩ := killV h₃ ht₃ (E := E01) hv₃
  -- Kill 4: a `u`-form detected at `E₁₀`, substituting `A` along `E₁₀`.
  obtain ⟨t₄, ht₄, hu₄, -, -⟩ :=
    exists_triple_of_ne_zero h₄ (X := E10) (Y := E00) (Z := E01)
      (by
        show mulTrace K E10
          ((E00 - ((t₃.v E01)⁻¹ * t₃.v E00) • E01) -
            ((t₂.v E11)⁻¹ * t₂.v (E00 - ((t₃.v E01)⁻¹ * t₃.v E00) • E01)) • E11)
          (E01 - t₁.w E01 • E10) ≠ 0
        rw [trace_T4]; exact one_ne_zero)
  obtain ⟨L₅, hlen₅, h₅⟩ := killU h₄ ht₄ (E := E10) hu₄
  -- Kill 5: a `u`-form detected at `E₁₁`, substituting `A` along `E₁₁`.
  obtain ⟨t₅, ht₅, hu₅, -, -⟩ :=
    exists_triple_of_ne_zero h₅ (X := E11) (Y := E10) (Z := E01)
      (by
        show mulTrace K (E11 - ((t₄.u E10)⁻¹ * t₄.u E11) • E10)
          ((E10 - ((t₃.v E01)⁻¹ * t₃.v E10) • E01) -
            ((t₂.v E11)⁻¹ * t₂.v (E10 - ((t₃.v E01)⁻¹ * t₃.v E10) • E01)) • E11)
          (E01 - t₁.w E01 • E10) ≠ 0
        rw [trace_T5]; exact one_ne_zero)
  obtain ⟨L₆, hlen₆, h₆⟩ := killU h₅ ht₅ (E := E11) hu₅
  -- The two surviving slices.
  have hsA : ∀ A : Matrix (Fin 2) (Fin 2) K,
      (L₆.map fun t => t.u A * t.v E00 * t.w E00).sum = A 0 0 := by
    intro A
    have hh := h₆ A E00 E00
    rw [hh]
    show mulTrace K
      ((A - ((t₅.u E11)⁻¹ * t₅.u A) • E11) -
        ((t₄.u E10)⁻¹ * t₄.u (A - ((t₅.u E11)⁻¹ * t₅.u A) • E11)) • E10)
      ((E00 - ((t₃.v E01)⁻¹ * t₃.v E00) • E01) -
        ((t₂.v E11)⁻¹ * t₂.v (E00 - ((t₃.v E01)⁻¹ * t₃.v E00) • E01)) • E11)
      (E00 - t₁.w E00 • E10) = A 0 0
    rw [hw100, zero_smul, sub_zero]
    exact trace_sliceA A _ _ _ _
  have hsB : ∀ A : Matrix (Fin 2) (Fin 2) K,
      (L₆.map fun t => t.u A * t.v E10 * t.w E00).sum = A 0 1 := by
    intro A
    have hh := h₆ A E10 E00
    rw [hh]
    show mulTrace K
      ((A - ((t₅.u E11)⁻¹ * t₅.u A) • E11) -
        ((t₄.u E10)⁻¹ * t₄.u (A - ((t₅.u E11)⁻¹ * t₅.u A) • E11)) • E10)
      ((E10 - ((t₃.v E01)⁻¹ * t₃.v E10) • E01) -
        ((t₂.v E11)⁻¹ * t₂.v (E10 - ((t₃.v E01)⁻¹ * t₃.v E10) • E01)) • E11)
      (E00 - t₁.w E00 • E10) = A 0 1
    rw [hw100, zero_smul, sub_zero]
    exact trace_sliceB A _ _ _ _
  -- Length bookkeeping: at most one term survives.
  have hlenL : (L.map fun t : Triple K =>
      (⟨t.u ∘ₗ mulLeftLM P', t.v ∘ₗ mulRightLM R', t.w ∘ₗ sandwichLM R P⟩ : Triple K)).length =
      L.length := List.length_map _
  have hL₆ : L₆.length ≤ 1 := by omega
  -- A list of length at most one cannot compute both slices.
  match L₆, hL₆, hsA, hsB with
  | [], _, hsA, _ =>
      have h1 := hsA (E00 (K := K))
      simp [E00] at h1
  | [ta], _, hsA, hsB =>
      have e1 : ta.u E00 * ta.v E00 * ta.w E00 = 1 := by
        simpa [E00] using hsA (E00 (K := K))
      have e2 : ta.u E00 * ta.v E10 * ta.w E00 = 0 := by
        simpa [E00] using hsB (E00 (K := K))
      have e3 : ta.u E01 * ta.v E10 * ta.w E00 = 1 := by
        simpa [E01] using hsB (E01 (K := K))
      have hne : ta.u E00 * ta.v E00 * ta.w E00 ≠ 0 := by
        rw [e1]; exact one_ne_zero
      have hu00 : ta.u E00 ≠ 0 := by
        intro h0; exact hne (by rw [h0, zero_mul, zero_mul])
      have hw00 : ta.w E00 ≠ 0 := by
        intro h0; exact hne (by rw [h0, mul_zero])
      have hv10 : ta.v E10 = 0 := by
        rcases mul_eq_zero.mp e2 with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' hu00
          · exact h''
        · exact absurd h' hw00
      rw [hv10, mul_zero, zero_mul] at e3
      exact zero_ne_one e3

end Winograd

/-! ### The invertible-hyperplane lemma (candidate shared lemma) -/

/-- **Invertible-hyperplane lemma.**  For every coefficient matrix `B` over a field there is an
invertible `2 × 2` matrix `A` annihilated by the entrywise pairing `∑ᵢⱼ B i j * A i j`; for
nonzero `B` this says every linear hyperplane of `2 × 2` matrices contains an invertible matrix.

Proof sketch: fully constructive case analysis on the entries of `B`.  If `B 0 1 ≠ 0` the
unitriangular matrix `!![1, -(B 0 0 + B 1 1) / B 0 1; 0, 1]` works; if `B 1 0 ≠ 0`, its
transpose analogue; and if both off-diagonal entries vanish the rotation `!![0, 1; -1, 0]`
pairs to `B 0 1 - B 1 0 = 0` regardless of the diagonal of `B`.  All inverses are explicit, so
no determinant theory is required. -/
theorem exists_isUnit_sum_entry_mul_eq_zero {K : Type u} [Field K]
    (B : Matrix (Fin 2) (Fin 2) K) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, IsUnit A ∧
      ∑ i : Fin 2, ∑ j : Fin 2, B i j * A i j = 0 := by
  by_cases h01 : B 0 1 ≠ 0
  · refine ⟨!![1, -(B 0 0 + B 1 1) / B 0 1; 0, 1], ?_, ?_⟩
    · refine ⟨⟨!![1, -(B 0 0 + B 1 1) / B 0 1; 0, 1],
        !![1, (B 0 0 + B 1 1) / B 0 1; 0, 1], ?_, ?_⟩, rfl⟩ <;>
        · ext i j
          fin_cases i <;> fin_cases j <;>
            · try simp [Matrix.mul_apply, Fin.sum_univ_two]
              try field_simp
              try ring
    · rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      try simp
      try field_simp
      try ring
  · push Not at h01
    by_cases h10 : B 1 0 ≠ 0
    · refine ⟨!![1, 0; -(B 0 0 + B 1 1) / B 1 0, 1], ?_, ?_⟩
      · refine ⟨⟨!![1, 0; -(B 0 0 + B 1 1) / B 1 0, 1],
          !![1, 0; (B 0 0 + B 1 1) / B 1 0, 1], ?_, ?_⟩, rfl⟩ <;>
          · ext i j
            fin_cases i <;> fin_cases j <;>
              · try simp [Matrix.mul_apply, Fin.sum_univ_two]
                try field_simp
                try ring
      · rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
        try simp
        try field_simp
        try ring
    · push Not at h10
      refine ⟨!![0, 1; -1, 0], ?_, ?_⟩
      · refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], ?_, ?_⟩, rfl⟩ <;>
          · ext i j
            fin_cases i <;> fin_cases j <;>
              simp [Matrix.mul_apply, Fin.sum_univ_two]
      · rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
        simp [h01, h10]

/-! ### The bridge from tensor rank certificates to trilinear decompositions -/

namespace Winograd

variable {K : Type u} [Field K]

/-- The covector on the coordinate space `(Fin 2 × Fin 2) → K` pairing entrywise against the
matrix `A`. -/
private def covOfMat (A : Matrix (Fin 2) (Fin 2) K) : ((Fin 2 × Fin 2) → K) →ₗ[K] K :=
  ∑ p : Fin 2 × Fin 2, A p.1 p.2 • LinearMap.proj p

private theorem covOfMat_apply (A : Matrix (Fin 2) (Fin 2) K) (v : (Fin 2 × Fin 2) → K) :
    covOfMat A v = ∑ p : Fin 2 × Fin 2, A p.1 p.2 * v p := by
  simp [covOfMat, smul_eq_mul]

private theorem covOfMat_single (A : Matrix (Fin 2) (Fin 2) K) (q : Fin 2 × Fin 2) :
    covOfMat A (Pi.single q 1) = A q.1 q.2 := by
  classical
  rw [covOfMat_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

/-- The entry-evaluation linear form on `2 × 2` matrices. -/
private def entryLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) K →ₗ[K] K where
  toFun A := A i j
  map_add' A B := by simp
  map_smul' s A := by simp

@[local simp] private theorem entryLM_apply (i j : Fin 2) (A : Matrix (Fin 2) (Fin 2) K) :
    entryLM i j A = A i j := rfl

/-- The linear form on `2 × 2` matrices pairing entrywise against the coordinate vector `x`. -/
private def vecForm (x : (Fin 2 × Fin 2) → K) : Matrix (Fin 2) (Fin 2) K →ₗ[K] K :=
  ∑ p : Fin 2 × Fin 2, x p • entryLM p.1 p.2

private theorem vecForm_apply (x : (Fin 2 × Fin 2) → K) (A : Matrix (Fin 2) (Fin 2) K) :
    vecForm x A = ∑ p : Fin 2 × Fin 2, x p * A p.1 p.2 := by
  simp [vecForm, smul_eq_mul]

/-- The two directions of the entrywise pairing agree. -/
private theorem vecForm_eq_covOfMat (x : (Fin 2 × Fin 2) → K) (A : Matrix (Fin 2) (Fin 2) K) :
    vecForm x A = covOfMat A x := by
  rw [vecForm_apply, covOfMat_apply]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-- The trace of `A * B * C` as the sum over matrix-multiplication index triples. -/
private theorem trace_eq_sum_triple (A B C : Matrix (Fin 2) (Fin 2) K) :
    (A * B * C).trace = ∑ a : MMTriple 2 2 2, A a.1 a.2.1 * B a.2.1 a.2.2 * C a.2.2 a.1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The full contraction of the matrix-multiplication tensor `⟨2,2,2⟩` against the three
entrywise covectors of matrices `A`, `B`, `C` is the trace of `A * B * C`. -/
private theorem covOfMat_contractX_mm (A B C : Matrix (Fin 2) (Fin 2) K) :
    covOfMat A (contractX (covOfMat B) (covOfMat C)
      (matrixMultiplication (K := K) 2 2 2)) = (A * B * C).trace := by
  unfold matrixMultiplication
  rw [map_sum, map_sum, trace_eq_sum_triple]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases a with ⟨i, j, k⟩
  rw [contractX_pure, map_smul, smul_eq_mul]
  have hX : covOfMat A (mmTermOfTriple (K := K) 2 2 2 (i, j, k) .X) = A i j := by
    simpa [mmTermOfTriple, mmTerm] using covOfMat_single A (i, j)
  have hY : covOfMat B (mmTermOfTriple (K := K) 2 2 2 (i, j, k) .Y) = B j k := by
    simpa [mmTermOfTriple, mmTerm] using covOfMat_single B (j, k)
  have hZ : covOfMat C (mmTermOfTriple (K := K) 2 2 2 (i, j, k) .Z) = C k i := by
    simpa [mmTermOfTriple, mmTerm] using covOfMat_single C (k, i)
  rw [hX, hY, hZ]
  ring

/-- The full contraction of a sum of pure tensors against the three entrywise covectors is the
corresponding sum of products of paired linear forms. -/
private theorem covOfMat_contractX_list_sum
    (terms : List (∀ c, MMSpace K 2 2 2 c)) (A B C : Matrix (Fin 2) (Fin 2) K) :
    covOfMat A (contractX (covOfMat B) (covOfMat C)
        ((terms.map (Tensor.pure (K := K))).sum)) =
      (terms.map fun x => vecForm (x .X) A * vecForm (x .Y) B * vecForm (x .Z) C).sum := by
  rw [map_list_sum, map_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, contractX_pure, map_smul, smul_eq_mul]
  rw [vecForm_eq_covOfMat, vecForm_eq_covOfMat, vecForm_eq_covOfMat]
  ring

/-- Every rank certificate of length at most `r` for the tensor `⟨2,2,2⟩` produces a list of at
most `r` rank-one trilinear terms computing the matrix trace form `(A,B,C) ↦ trace (A*B*C)`.

Proof sketch: pair each leg of every pure term of the certificate with the entrywise covector
of the corresponding matrix argument.  The resulting scalar identity is the full contraction of
the tensor equality underlying the certificate, computed on the matrix-multiplication side by
`covOfMat_contractX_mm` and on the certificate side by `covOfMat_contractX_list_sum`. -/
theorem computes_of_rankLE {r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) 2 2 2)) :
    ∃ L : List (Triple K), L.length ≤ r ∧ Computes (mulTrace K) L := by
  obtain ⟨terms, hlen, hsum⟩ := h
  refine ⟨terms.map fun x => ⟨vecForm (x .X), vecForm (x .Y), vecForm (x .Z)⟩,
    by simpa using hlen, ?_⟩
  intro A B C
  rw [List.map_map]
  have hlist := covOfMat_contractX_list_sum terms A B C
  rw [← hsum] at hlist
  rw [covOfMat_contractX_mm] at hlist
  exact (congrArg _ rfl).trans hlist.symm

end Winograd

/-! ### Final theorems -/

/-- **Winograd's lower bound** (Winograd 1971; Hopcroft–Kerr 1971 over `𝔽₂`): every
constructive rank certificate for the `2 × 2` matrix-multiplication tensor has length at least
seven, over every field. -/
theorem matrixMultiplication_two_rank_lower_seven {K : Type u} [Field K] {r : ℕ}
    (h : Tensor.RankLE r (matrixMultiplication (K := K) 2 2 2)) : 7 ≤ r := by
  obtain ⟨L, hlen, hcomp⟩ := Winograd.computes_of_rankLE h
  exact le_trans hcomp.length_ge_seven hlen

/-- The rank of the `2 × 2` matrix-multiplication tensor is at least seven, over every
field. -/
theorem seven_le_rank_matrixMultiplication_two {K : Type u} [Field K] :
    7 ≤ Tensor.rank (matrixMultiplication (K := K) 2 2 2) :=
  matrixMultiplication_two_rank_lower_seven (Tensor.rank_spec _)

/-- **The rank of `2 × 2` matrix multiplication is exactly seven** over every field: Strassen's
decomposition (upper bound) meets Winograd's lower bound. -/
theorem rank_matrixMultiplication_two {K : Type u} [Field K] :
    Tensor.rank (matrixMultiplication (K := K) 2 2 2) = 7 :=
  le_antisymm (Tensor.rank_le_iff.mpr (Examples.strassen_rankLE K))
    seven_le_rank_matrixMultiplication_two

end AlgebraicComplexity
