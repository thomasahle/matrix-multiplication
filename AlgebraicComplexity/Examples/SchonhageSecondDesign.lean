/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.MatrixMultiplication.PartialAsymptoticSum
import Mathlib.Tactic.IntervalCases

/-!
# Schönhage's second design for partial matrix multiplication

This regression client formalizes the two-parameter family of partial matrix-multiplication
patterns of Arnold Schönhage, *Partial and Total Matrix Multiplication*, SIAM Journal on
Computing **10**(3), 434–455 (1981), §5, equations (5.5)–(5.8), p. 446 (Figure 5.2 displays the
pattern for `k = 4`, `q = 3`).

With `m = q + 1` inner indices and `n = 1 + (k − 1)(q − 1)` output columns, the design fills

* the `k × m` left factor in every position except the first column below its top entry, i.e. at
  `I = {(κ, μ) | κ = 0 ∨ μ ≠ 0}` (`sdLeftPositions`), and
* the `m × n` right factor in its first row and its first column only, i.e. at
  `J = {(μ, ν) | μ = 0 ∨ ν = 0}` (`sdRightPositions`).

The right-hand pattern does not in fact depend on `k`, so `sdRightPositions` takes the number of
columns `n` as an independent parameter and `sdColumns k q = 1 + (k − 1)(q − 1)` names Schönhage's
choice.  Keeping `n` opaque also keeps the `k = q = 2` instance on the literal index type
`Fin 2` rather than on `Fin (1 + (2 − 1) * (2 − 1))`.

## Objects and results

* `sdLeftPositions`, `sdRightPositions`, `sdColumns`: the pattern of equations (5.5)/(5.6).
* `card_pmmColumn_sdLeftPositions`, `card_pmmRow_sdRightPositions`: Schönhage's column counts
  `k₀ = 1`, `k_j = k` for `j ≠ 0` and row counts `n₀ = n`, `n_j = 1` for `j ≠ 0`.
* `sum_pmmColumn_card_sd`: the left factor carries `k q + 1` variables in total — the length of
  the approximate decomposition (5.8).
* `card_pmmSupport_sd`, `card_pmmSupport_secondDesign`: the number of ones is
  `f = 1 + (k − 1)(q − 1) + k q = 2 + 2kq − k − q`, the count displayed below (5.7).
* `sdBorderTerms`, `sdBorderPath`, `sd_borderRankLEAt`: **at `k = q = 2`** the explicit
  five-term approximate decomposition of order `2` given by (5.8), over every commutative ring.
  This is the identity Coppersmith reuses in *Rapid multiplication of rectangular matrices*,
  SIAM J. Comput. **11**(3), 467–471 (1982), p. 467.
* `sd_omega_le`, `sd_omega_lt`: the resulting exponent bound `ω ≤ 3 log 5 / log 6 < 2.695` over
  every infinite field, through Schönhage's Theorem 4.1
  (`omega_le_of_borderRankLE_partialMatrixMultiplication`).
* `omega_le_of_borderRankLE_secondDesign`: the general exponent formula (5.9),
  `λ(l, f) = 3 log (kq + 1) / log (2 + 2kq − k − q)`, stated **conditionally** on the general
  border-rank certificate; see the non-goals below.

## The certificate

Write `α = a₀₀`, `A_{κμ} = a_{κ,μ+1}`, `B_μ = b_{μ+1,0}`, `β_ν = b_{0,ν}`, `C_κ = c_{0,κ}`,
`γ_ν = c_{ν,0}` for the variables of the pattern, so that `γ₀ = C₀` is the single shared
variable and the tensor of (5.7) reads

`T = ∑_ν α β_ν γ_ν + ∑_{κ,μ} A_{κμ} B_μ C_κ`,

an inner product of length `n` in `β, γ` scaled by `α`, linked to the `⟨k, q, 1⟩` matrix–vector
product in `A, B, C`.  Indexing the `k q` main curves by `(κ, μ)` and adding one cancellation
curve, (5.8) reads

`∑_{κ,μ} (α + ε² A_{κμ}) (B_μ + ε V_{κμ} + ε² W_{κμ}) (C_κ + ε U_{κμ})
   − α (∑_μ B_μ) (∑_κ C_κ) = ε² T + O(ε³)`,

where `W` is `β₀` at `(κ, μ) = (0, 0)` and `0` elsewhere, and `U, V` are the discrete
"circulation" fields carrying the `n − 1 = (k − 1)(q − 1)` remaining inner-product variables:
`V_{κμ} = β_{ν(κ,μ)}` and `U_{κμ} = γ_{ν(κ,μ)}` on the cells with `κ ≠ 0 ≠ μ`, extended over the
first row and first column of cells so that every column of `U` and every row of `V` sums to
zero.  Those two vanishing conditions kill the `ε¹` slice, the cancellation curve kills the `ε⁰`
slice, and the `ε²` slice is exactly `T`: the terms `A_{κμ} B_μ C_κ` come from the `X`-leg
perturbation, the terms `α V_{κμ} U_{κμ}` from the two `ε¹` perturbations meeting, and the
linking term `α β₀ γ₀` from `W₀₀` against the constant `C₀ = γ₀`.

At `k = q = 2` this is Schönhage's displayed five-term identity verbatim; his first curve
`(a₀₀ + ε² a₀₁)(b₁₀ + ε² b₀₀) c₀₀` is `sdCurve₁` below.

## Non-goals

Only the instance `k = q = 2` of the decomposition is proved.  The general identity enters
`omega_le_of_borderRankLE_secondDesign` as a hypothesis; a proof for arbitrary `(k, q)` would
give Schönhage's (5.9) and its minimum `λ(17, 26) < 2.6087` at `k = q = 4`.  That value is
*weaker* than the bound `ω < 2.6` already available in
`AlgebraicComplexity/Examples/Schonhage.lean` from the disjoint form of the same design
(§6, Lemma 6.1 at `k = n = 3`), so the general case is a completeness item rather than a
numerical improvement.

Schönhage's §6 reformulation — the sharp value `R̲₂(⟨k,1,n⟩ ⊕ ⟨1,m,1⟩) = k n + 1` — is likewise
out of scope; its instance `k = n = 3` is `Examples/Schonhage.lean`.

## References

* A. Schönhage, *Partial and total matrix multiplication*, SIAM J. Comput. **10**(3) (1981),
  434--455.  §5, equations (5.5)--(5.9), pp. 445--447: the second design, its five-term
  approximate decomposition at `k = q = 2`, and the exponent formula; §4, Theorem 4.1: the partial
  asymptotic sum inequality that turns the decomposition into a bound on `ω`; §6, Lemma 6.1: the
  disjoint reformulation used by `Examples/Schonhage.lean`.
* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. **11**(3)
  (1982), 467--471, p. 467, which reuses the `k = q = 2` identity formalized here.
* D. Bini, M. Capovani, F. Romani, and G. Lotti, *O(n^2.7799) complexity for n × n approximate
  matrix multiplication*, Inform. Process. Lett. **8**(5) (1979), 234--235: the independent
  certificate that lands on the same pair `(l, f) = (5, 6)`, hence on the same value
  `λ(5, 6) = 3 log 5 / log 6` (`Analysis.three_mul_log_five_div_log_six_lt`).
-/

namespace AlgebraicComplexity.Analysis

/-! ## The numerical value of this design

`λ(5, 6) = 3 log 5 / log 6` is not a canonical constant: `(5, 6)` is the length/support pair of
*this* decomposition, so the enclosure belongs with its client rather than in
`Analysis/LogConstants.lean` (see that file's module doc).  It keeps the
`AlgebraicComplexity.Analysis` namespace because its statement is pure analysis and because
`AxiomAudit.lean` refers to it by that name.
-/

/-- **Schönhage's `λ(5, 6) < 2.695`**, from the exact integer comparison `5 ^ 177 < 6 ^ 159`.

`3 log 5 / log 6` is the exponent bound that Schönhage's partial asymptotic sum inequality
produces from any border-rank-five decomposition of a partial `2 × 2` pattern with six ones — both
Bini's five-term algorithm and Schönhage's second design at `k = q = 2` (`sd_omega_lt`, below)
land on it. -/
theorem three_mul_log_five_div_log_six_lt : 3 * Real.log 5 / Real.log 6 < 2.695 := by
  have hpowNat : (5 : ℕ) ^ 177 < (6 : ℕ) ^ 159 := by norm_num
  have hpow : ((5 : ℝ) ^ (177 : ℕ)) < ((6 : ℝ) ^ (159 : ℕ)) := by exact_mod_cast hpowNat
  have hlog := mul_log_lt_mul_log_of_pow_lt (by norm_num : (0 : ℝ) < 5) hpow
  norm_num at hlog
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hlog6]
  linarith

end AlgebraicComplexity.Analysis

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open Tensor.PolynomialVector

universe u

section Pattern

/-- The variable positions of the left factor in Schönhage's second design (1981, equation
(5.6)): the `k × (q+1)` pattern `I = {(κ, μ) | κ = 0 ∨ μ ≠ 0}`, that is, every position except
those of the first column strictly below its top entry. -/
def sdLeftPositions (k q : ℕ) : Finset (Fin k × Fin (q + 1)) :=
  Finset.univ.filter fun p ↦ (p.1 : ℕ) = 0 ∨ (p.2 : ℕ) ≠ 0

/-- The variable positions of the right factor in Schönhage's second design (1981, equation
(5.6)): the `(q+1) × n` pattern `J = {(μ, ν) | μ = 0 ∨ ν = 0}`, that is, the first row and the
first column only. -/
def sdRightPositions (q n : ℕ) : Finset (Fin (q + 1) × Fin n) :=
  Finset.univ.filter fun p ↦ (p.1 : ℕ) = 0 ∨ (p.2 : ℕ) = 0

/-- Schönhage's choice of the number of output columns in the second design (1981, equation
(5.5)): `n = 1 + (k − 1)(q − 1)`. -/
def sdColumns (k q : ℕ) : ℕ := 1 + (k - 1) * (q - 1)

@[simp] theorem mem_sdLeftPositions {k q : ℕ} {p : Fin k × Fin (q + 1)} :
    p ∈ sdLeftPositions k q ↔ (p.1 : ℕ) = 0 ∨ (p.2 : ℕ) ≠ 0 := by
  simp [sdLeftPositions]

@[simp] theorem mem_sdRightPositions {q n : ℕ} {p : Fin (q + 1) × Fin n} :
    p ∈ sdRightPositions q n ↔ (p.1 : ℕ) = 0 ∨ (p.2 : ℕ) = 0 := by
  simp [sdRightPositions]

/-- The number of output columns is positive. -/
theorem sdColumns_pos (k q : ℕ) : 0 < sdColumns k q :=
  lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 _)

/-- At `k = q = 2` the second design has two output columns. -/
theorem sdColumns_two_two : sdColumns 2 2 = 2 := by
  norm_num [sdColumns]

/-- Schönhage's column counts for the second design: the first column of the left factor carries
one variable, every other column carries all `k`. -/
theorem card_pmmColumn_sdLeftPositions {k q : ℕ} (hk : 0 < k) (j : Fin (q + 1)) :
    (pmmColumn (sdLeftPositions k q) j).card = if (j : ℕ) = 0 then 1 else k := by
  classical
  by_cases hj : (j : ℕ) = 0
  · rw [if_pos hj]
    have hset : pmmColumn (sdLeftPositions k q) j = {(⟨0, hk⟩ : Fin k)} := by
      ext x
      simp [hj, Fin.ext_iff]
    rw [hset, Finset.card_singleton]
  · rw [if_neg hj]
    have hset : pmmColumn (sdLeftPositions k q) j = (Finset.univ : Finset (Fin k)) := by
      ext x
      simp [hj]
    rw [hset, Finset.card_univ, Fintype.card_fin]

/-- Schönhage's row counts for the second design: the first row of the right factor carries all
`n` variables, every other row carries exactly one. -/
theorem card_pmmRow_sdRightPositions {q n : ℕ} (hn : 0 < n) (j : Fin (q + 1)) :
    (pmmRow (sdRightPositions q n) j).card = if (j : ℕ) = 0 then n else 1 := by
  classical
  by_cases hj : (j : ℕ) = 0
  · rw [if_pos hj]
    have hset : pmmRow (sdRightPositions q n) j = (Finset.univ : Finset (Fin n)) := by
      ext y
      simp [hj]
    rw [hset, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hj]
    have hset : pmmRow (sdRightPositions q n) j = {(⟨0, hn⟩ : Fin n)} := by
      ext y
      simp [hj, Fin.ext_iff]
    rw [hset, Finset.card_singleton]

/-- Every column of the left factor of the second design carries a variable. -/
theorem pmmColumn_sdLeftPositions_card_pos {k q : ℕ} (hk : 0 < k) (j : Fin (q + 1)) :
    0 < (pmmColumn (sdLeftPositions k q) j).card := by
  rw [card_pmmColumn_sdLeftPositions hk]
  split
  · exact Nat.one_pos
  · exact hk

/-- Every row of the right factor of the second design carries a variable. -/
theorem pmmRow_sdRightPositions_card_pos {q n : ℕ} (hn : 0 < n) (j : Fin (q + 1)) :
    0 < (pmmRow (sdRightPositions q n) j).card := by
  rw [card_pmmRow_sdRightPositions hn]
  split
  · exact hn
  · exact Nat.one_pos

/-- The left factor of the second design carries `k q + 1` variables in total.  This is exactly
the length of Schönhage's approximate decomposition (5.8): one curve per inner index and left row
outside the top-left corner, plus one cancellation curve. -/
theorem sum_pmmColumn_card_sd {k q : ℕ} (hk : 0 < k) :
    ∑ j : Fin (q + 1), (pmmColumn (sdLeftPositions k q) j).card = k * q + 1 := by
  simp only [card_pmmColumn_sdLeftPositions hk]
  rw [Fin.sum_univ_succ]
  have h0 : (if (((0 : Fin (q + 1)) : ℕ)) = 0 then 1 else k) = 1 := by simp
  have hs : ∀ i : Fin q, (if ((i.succ : Fin (q + 1)) : ℕ) = 0 then 1 else k) = k := fun i ↦
    if_neg (by simp)
  rw [h0]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Nat.mul_comm q k, Nat.add_comm]

/-- **Schönhage's count for the second design** (1981, the line below equation (5.7)): the
pattern contains `f = n + k q` ones. -/
theorem card_pmmSupport_sd {k q n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (pmmSupport (sdLeftPositions k q) (sdRightPositions q n)).card = n + k * q := by
  rw [card_pmmSupport]
  have hterm : ∀ j : Fin (q + 1),
      (pmmColumn (sdLeftPositions k q) j).card * (pmmRow (sdRightPositions q n) j).card =
        if (j : ℕ) = 0 then n else k := by
    intro j
    rw [card_pmmColumn_sdLeftPositions hk, card_pmmRow_sdRightPositions hn]
    by_cases hj : (j : ℕ) = 0 <;> simp [hj]
  simp only [hterm]
  rw [Fin.sum_univ_succ]
  have h0 : (if (((0 : Fin (q + 1)) : ℕ)) = 0 then n else k) = n := by simp
  have hs : ∀ i : Fin q, (if ((i.succ : Fin (q + 1)) : ℕ) = 0 then n else k) = k := fun i ↦
    if_neg (by simp)
  rw [h0]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Nat.mul_comm q k]

/-- Schönhage's count at his own choice of `n`: the second design contains
`f = 1 + (k − 1)(q − 1) + k q` ones, that is `2 + 2kq − k − q`. -/
theorem card_pmmSupport_secondDesign {k q : ℕ} (hk : 0 < k) :
    (pmmSupport (sdLeftPositions k q) (sdRightPositions q (sdColumns k q))).card =
      1 + (k - 1) * (q - 1) + k * q := by
  rw [card_pmmSupport_sd hk (sdColumns_pos k q), sdColumns]

end Pattern

section Certificate

variable (K : Type u) [CommRing K]

/-- Left-factor variable `a_{i,j}` of the second design at `k = q = 2`. -/
def sdVarA (i : Fin 2) (j : Fin 3) : PMMSpace (Fin 2) (Fin 3) (Fin 2) K .X :=
  Pi.single (i, j) 1

/-- Right-factor variable `b_{j,v}` of the second design at `k = q = 2`. -/
def sdVarB (j : Fin 3) (v : Fin 2) : PMMSpace (Fin 2) (Fin 3) (Fin 2) K .Y :=
  Pi.single (j, v) 1

/-- Output variable `c_{v,i}` of the second design at `k = q = 2`. -/
def sdVarC (v : Fin 2) (i : Fin 2) : PMMSpace (Fin 2) (Fin 3) (Fin 2) K .Z :=
  Pi.single (v, i) 1

/-- The defining pure summand of the partial tensor, in the variable names of this file.  Both
sides are the same triple of standard basis vectors; they differ only in which `DecidableEq`
instance `Pi.single` was elaborated with, so the identification is definitional. -/
theorem pmmTerm_eq_sdVar (i : Fin 2) (j : Fin 3) (v : Fin 2) :
    pmmTerm (K := K) (i, j, v) = ofLegs (sdVarA K i j) (sdVarB K j v) (sdVarC K v i) := by
  funext c
  cases c <;> rfl

/-- The six ones of the second design at `k = q = 2`, read off from the support of the pattern.
The first two summands form the linked inner product `α (β₀ γ₀ + β₁ γ₁)`, the last four the
matrix–vector product `⟨2, 2, 1⟩`. -/
theorem sd_partialMatrixMultiplication_eq :
    partialMatrixMultiplication (K := K) (sdLeftPositions 2 2) (sdRightPositions 2 2) =
      pure (K := K) (ofLegs (sdVarA K 0 0) (sdVarB K 0 0) (sdVarC K 0 0)) +
        (pure (K := K) (ofLegs (sdVarA K 0 0) (sdVarB K 0 1) (sdVarC K 1 0)) +
          (pure (K := K) (ofLegs (sdVarA K 0 1) (sdVarB K 1 0) (sdVarC K 0 0)) +
            (pure (K := K) (ofLegs (sdVarA K 0 2) (sdVarB K 2 0) (sdVarC K 0 0)) +
              (pure (K := K) (ofLegs (sdVarA K 1 1) (sdVarB K 1 0) (sdVarC K 0 1)) +
                pure (K := K) (ofLegs (sdVarA K 1 2) (sdVarB K 2 0) (sdVarC K 0 1)))))) := by
  have hsupp : pmmSupport (sdLeftPositions 2 2) (sdRightPositions 2 2) =
      ({(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 2, 0), (1, 1, 0), (1, 2, 0)} :
        Finset (Fin 2 × Fin 3 × Fin 2)) := by decide
  unfold partialMatrixMultiplication
  rw [hsupp, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rfl

/-- First curve of Schönhage's five-term decomposition (5.8) at `k = q = 2`:
`(a₀₀ + ε² a₀₁)(b₁₀ + ε² b₀₀) c₀₀`. -/
noncomputable def sdCurve₁ : ∀ c, PolynomialVector (PMMSpace (Fin 2) (Fin 3) (Fin 2) K c) :=
  ofLegs (constant (sdVarA K 0 0) + monomial 2 (sdVarA K 0 1))
    (constant (sdVarB K 1 0) + monomial 2 (sdVarB K 0 0))
    (constant (sdVarC K 0 0))

/-- Second curve of (5.8) at `k = q = 2`: `(a₀₀ + ε² a₀₂) b₂₀ (c₀₀ − ε c₁₀)`. -/
noncomputable def sdCurve₂ : ∀ c, PolynomialVector (PMMSpace (Fin 2) (Fin 3) (Fin 2) K c) :=
  ofLegs (constant (sdVarA K 0 0) + monomial 2 (sdVarA K 0 2))
    (constant (sdVarB K 2 0))
    (constant (sdVarC K 0 0) + monomial 1 (-sdVarC K 1 0))

/-- Third curve of (5.8) at `k = q = 2`: `(a₀₀ + ε² a₁₁)(b₁₀ − ε b₀₁) c₀₁`. -/
noncomputable def sdCurve₃ : ∀ c, PolynomialVector (PMMSpace (Fin 2) (Fin 3) (Fin 2) K c) :=
  ofLegs (constant (sdVarA K 0 0) + monomial 2 (sdVarA K 1 1))
    (constant (sdVarB K 1 0) + monomial 1 (-sdVarB K 0 1))
    (constant (sdVarC K 0 1))

/-- Fourth curve of (5.8) at `k = q = 2`: `(a₀₀ + ε² a₁₂)(b₂₀ + ε b₀₁)(c₀₁ + ε c₁₀)`. -/
noncomputable def sdCurve₄ : ∀ c, PolynomialVector (PMMSpace (Fin 2) (Fin 3) (Fin 2) K c) :=
  ofLegs (constant (sdVarA K 0 0) + monomial 2 (sdVarA K 1 2))
    (constant (sdVarB K 2 0) + monomial 1 (sdVarB K 0 1))
    (constant (sdVarC K 0 1) + monomial 1 (sdVarC K 1 0))

/-- Cancellation curve of (5.8) at `k = q = 2`: `−a₀₀ (b₁₀ + b₂₀)(c₀₀ + c₀₁)`.  It carries no
`ε` and exists only to kill the `ε⁰` slice of the four main curves. -/
noncomputable def sdCancellationCurve :
    ∀ c, PolynomialVector (PMMSpace (Fin 2) (Fin 3) (Fin 2) K c) :=
  ofLegs (constant (sdVarA K 0 0))
    (constant (-(sdVarB K 1 0 + sdVarB K 2 0)))
    (constant (sdVarC K 0 0 + sdVarC K 0 1))

/-- The five polynomial pure tensors of Schönhage's second design at `k = q = 2`. -/
noncomputable def sdBorderTerms :
    List (∀ c, PolynomialVector (PMMSpace (Fin 2) (Fin 3) (Fin 2) K c)) :=
  [sdCurve₁ K, sdCurve₂ K, sdCurve₃ K, sdCurve₄ K, sdCancellationCurve K]

@[simp] theorem sdBorderTerms_length : (sdBorderTerms K).length = 5 := by
  simp [sdBorderTerms]

/-- The polynomial tensor path of Schönhage's second design at `k = q = 2`. -/
noncomputable def sdBorderPath : PolynomialTensor K (PMMSpace (Fin 2) (Fin 3) (Fin 2) K) :=
  ((sdBorderTerms K).map (polynomialPure (K := K))).sum

/-- The constant slice of the certificate cancels: the four main curves contribute
`α (B₀ + B₁)(C₀ + C₁)` and the cancellation curve subtracts it. -/
theorem sdBorderPath_coeff_zero : sdBorderPath K 0 = 0 := by
  simp [sdBorderPath, sdBorderTerms, sdCurve₁, sdCurve₂, sdCurve₃, sdCurve₄,
    sdCancellationCurve, constant]
  abel

/-- The linear slice of the certificate cancels: every column of the `U`-field and every row of
the `V`-field sums to zero. -/
theorem sdBorderPath_coeff_one : sdBorderPath K 1 = 0 := by
  simp [sdBorderPath, sdBorderTerms, sdCurve₁, sdCurve₂, sdCurve₃, sdCurve₄,
    sdCancellationCurve, constant]

/-- The quadratic slice of the certificate is the partial tensor of the second design. -/
theorem sdBorderPath_coeff_two :
    sdBorderPath K 2 =
      partialMatrixMultiplication (K := K) (sdLeftPositions 2 2) (sdRightPositions 2 2) := by
  rw [sd_partialMatrixMultiplication_eq]
  simp [sdBorderPath, sdBorderTerms, sdCurve₁, sdCurve₂, sdCurve₃, sdCurve₄,
    sdCancellationCurve, constant]
  abel

/-- **Schönhage's second design at `k = q = 2`** (1981, equations (5.5)–(5.8)): the partial
`2 × 3` by `3 × 2` product with the pattern `sdLeftPositions 2 2` / `sdRightPositions 2 2` has an
approximate decomposition of order `2` and length `k q + 1 = 5`, over every commutative ring.

This is the identity Coppersmith displays in *Rapid multiplication of rectangular matrices*
(SIAM J. Comput. 11(3), 1982, p. 467) as the starting point of the first bound `α > 0`. -/
theorem sd_borderRankLEAt :
    BorderRankLEAt 5 2
      (partialMatrixMultiplication (K := K) (sdLeftPositions 2 2) (sdRightPositions 2 2)) := by
  refine ⟨sdBorderTerms K, by simp, ?_⟩
  refine ⟨sdBorderPath_coeff_two K, ?_⟩
  intro d hd
  interval_cases d
  · exact sdBorderPath_coeff_zero K
  · exact sdBorderPath_coeff_one K

/-- Certificate-facing corollary: `R̲ ≤ 5` for the second design at `k = q = 2`. -/
theorem sd_borderRankLE :
    BorderRankLE 5
      (partialMatrixMultiplication (K := K) (sdLeftPositions 2 2) (sdRightPositions 2 2)) :=
  (sd_borderRankLEAt K).toBorderRankLE

end Certificate

section Exponent

/-- The second design at `k = q = 2` has six ones. -/
theorem card_pmmSupport_sd_two :
    (pmmSupport (sdLeftPositions 2 2) (sdRightPositions 2 2)).card = 6 := by
  rw [card_pmmSupport_sd (by norm_num) (by norm_num)]

/-- **Schönhage's second design gives `ω ≤ 3 log 5 / log 6`** over every infinite field.

The five-term order-two decomposition `sd_borderRankLE` of a pattern with `f = 6` ones feeds
Schönhage's Theorem 4.1 (`omega_le_of_borderRankLE_partialMatrixMultiplication`) with `l = 5`.
The value `λ(5, 6)` coincides with the one obtained from Bini's five-term algorithm in
`AlgebraicComplexity/Examples/Bini.lean`; the two certificates are genuinely different algorithms
for different patterns that happen to share the pair `(l, f) = (5, 6)`. -/
theorem sd_omega_le (F : Type u) [Field F] [Infinite F] :
    omega F ≤ 3 * Real.log 5 / Real.log 6 := by
  have hmain := omega_le_of_borderRankLE_partialMatrixMultiplication F
    (sdLeftPositions 2 2) (sdRightPositions 2 2)
    (pmmColumn_sdLeftPositions_card_pos (by norm_num))
    (pmmRow_sdRightPositions_card_pos (by norm_num))
    (by rw [card_pmmSupport_sd_two]; norm_num) (by norm_num) (sd_borderRankLE F)
  rw [card_pmmSupport_sd_two] at hmain
  exact_mod_cast hmain

/-- Numerical form: Schönhage's second design at `k = q = 2` gives `ω < 2.695`.

The numerical step is the named certificate `Analysis.three_mul_log_five_div_log_six_lt`,
`λ(5, 6) = 3 log 5 / log 6 < 2.695` from the exact integer comparison `5 ^ 177 < 6 ^ 159`.  The
same value arises from Bini's five-term algorithm in
`MatrixMultiplication/PartialAsymptoticSum.lean` (`omega_lt_of_borderRankLE_biniPartial`), which
keeps its own copy of the derivation: that module cannot import
`Analysis/LogConstants.lean` without pulling in `Mathlib.Analysis.SpecialFunctions.Log.Deriv`,
which pushes an unrelated `positivity`/`simp` step in it past `maxHeartbeats`. -/
theorem sd_omega_lt (F : Type u) [Field F] [Infinite F] : omega F < 2.695 :=
  lt_of_le_of_lt (sd_omega_le F) Analysis.three_mul_log_five_div_log_six_lt

/-- **Schönhage's exponent formula (5.9)**, conditional on the general certificate.

If the second design with parameters `(k, q)` admits an approximate decomposition of length
`k q + 1` — which Schönhage's (5.8) exhibits for all `k, q ≥ 2`, and which this file proves only
at `k = q = 2` (`sd_borderRankLE`) — then Theorem 4.1 gives

`ω ≤ λ(k q + 1, 1 + (k−1)(q−1) + k q) = 3 log (kq + 1) / log (2 + 2kq − k − q)`.

Schönhage minimizes this at `k = q = 4`, where it reads `λ(17, 26) = 2.6087…`.  That is weaker
than the unconditional `ω < 2.6` of `AlgebraicComplexity/Examples/Schonhage.lean`, so the
statement is recorded for completeness rather than as a numerical improvement. -/
theorem omega_le_of_borderRankLE_secondDesign (F : Type u) [Field F] [Infinite F]
    {k q : ℕ} (hk : 0 < k) (hf : 2 ≤ sdColumns k q + k * q)
    (h : BorderRankLE (k * q + 1)
      (partialMatrixMultiplication (K := F) (sdLeftPositions k q)
        (sdRightPositions q (sdColumns k q)))) :
    omega F ≤
      3 * Real.log ((k * q + 1 : ℕ) : ℝ) / Real.log ((sdColumns k q + k * q : ℕ) : ℝ) := by
  have hn : 0 < sdColumns k q := sdColumns_pos k q
  have hmain := omega_le_of_borderRankLE_partialMatrixMultiplication F
    (sdLeftPositions k q) (sdRightPositions q (sdColumns k q))
    (pmmColumn_sdLeftPositions_card_pos hk) (pmmRow_sdRightPositions_card_pos hn)
    (by rw [card_pmmSupport_sd hk hn]; exact hf) (Nat.le_add_left 1 (k * q)) h
  rwa [card_pmmSupport_sd hk hn] at hmain

end Exponent

end AlgebraicComplexity.Examples
