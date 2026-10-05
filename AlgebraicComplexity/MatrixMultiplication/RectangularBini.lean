/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.BiniInterpolation
import AlgebraicComplexity.MatrixMultiplication.RectangularCertificate

/-!
# Bini's interpolation principle for the rectangular exponent

`MatrixMultiplication/BiniInterpolation.lean` turns one border-rank certificate for the *square*
tensor `⟨q,q,q⟩` into the exponent bound `omega ≤ log r / log q`.  This module is the rectangular
counterpart: a single border-rank certificate for `⟨A, A, C⟩` with `A^κ ≤ C` gives

`rectangularOmega K κ ≤ log r / log A`,

with no covering hypothesis and no schedule for the caller to supply.  The leg normalization is
Huang--Pan's `ω(1, 1, κ)` — the *outer* dimension is the large one — which is what a laser-method
extraction produces and what `rectangularMatrixRankSequence_eq_rank_outer` identifies with the
`rectangularOmega` of `MatrixMultiplication/RectangularExponent.lean`.

## Principal results

* `Tensor.BorderRankLEAt.matrixMultiplication_pow_general`: the rectangular generalization of
  `Tensor.BorderRankLEAt.matrixMultiplication_pow`.  Only the square case was recorded, although
  its engine `matrixMultiplication_mul` is fully rectangular;
* `rectangularMatrixExponentLE_of_power_rank_exponentialBound`: the rectangular analogue of
  `matrixExponentLE_of_power_rank_exponentialBound`.  Rank bounds on the geometric family
  `⟨A^k, A^k, C^k⟩` that grow at exponential rate `ρ` give the admissible exponent
  `log ρ / log A`, because `Nat.clog A n` interpolates every scale `n` and `(A^k)^κ ≤ C^k`
  survives the ceiling in `rectangularMiddleDimension`;
* `rectangularOmega_le_log_of_borderRankLEAt` and `rectangularOmega_le_log_of_borderRankLE`:
  Bini's theorem in rectangular form.

## Design notes

A client of this module never has to exhibit an infinite family of certificates or a covering of
the scales.  `rectangularMatrixExponentLE_of_power_rank_exponentialBound` does that work inline,
by *powering* a single certificate: `⟨A,A,C⟩` powers to `⟨A^k, A^k, C^k⟩`, the scales `A^k` are
`Nat.clog`-dense, and the middle-dimension hypothesis `A^κ ≤ C` powers to
`(A^k)^κ = (A^κ)^k ≤ C^k`.  One certificate at one scale is enough, exactly as in the square case.

The general packager `rectangularOmega_le_of_certificates`
(`MatrixMultiplication/RectangularCertificate.lean`), which *does* take an explicit covering
hypothesis, is therefore not used anywhere in this module; the covering step is reproved here for
the geometric family so that this module's clients can stay covering-free.  The packager is for
clients whose certificate family is not the powers of a single certificate —
`Examples/CoppersmithRectangular1982.lean` is the one in the tree.

The interpolation loss `(k·d + 1)^3` of `Tensor.BorderRankLEAt.toRankLE` is absorbed by the
`ExponentialBound` slack `ρ = r·exp(ε·log A)`, the same device Bini's square proof uses.

## References

* D. Bini, M. Capovani, F. Romani, and G. Lotti, *O(n^2.7799) complexity for n × n approximate
  matrix multiplication*, Inform. Process. Lett. **8**(5) (1979), 234--235.  The source of the
  interpolation principle that turns an approximate (border-rank) algorithm into an exact one at
  a polynomial cost in the degree, which is what `Tensor.BorderRankLEAt.toRankLE` formalizes and
  what this module transports to the rectangular exponent.
* X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299.  The leg normalization `ω(1, 1, κ)` used here, matched
  to `rectangularOmega` by `rectangularMatrixRankSequence_eq_rank_outer`.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

variable {K : Type u} [CommSemiring K]

namespace Tensor.BorderRankLEAt

/-- **Powering a rectangular degree-aware border certificate.**  A certificate for `⟨m,n,p⟩`
powers to one for `⟨m^k, n^k, p^k⟩` with size `r^k` and degree `k·d`.

`Tensor.BorderRankLEAt.matrixMultiplication_pow` states only the square case, although the
multiplication law `matrixMultiplication_mul` it is built from is already rectangular. -/
theorem matrixMultiplication_pow_general {m n p r d : ℕ}
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) m n p)) (k : ℕ) :
    BorderRankLEAt (r ^ k) (k * d)
      (matrixMultiplication (K := K) (m ^ k) (n ^ k) (p ^ k)) := by
  induction k with
  | zero =>
      have hbase : BorderRankLEAt (m ^ 0 * n ^ 0 * p ^ 0) 0
          (matrixMultiplication (K := K) (m ^ 0) (n ^ 0) (p ^ 0)) :=
        RankLE.toBorderRankLEAt
          (matrixMultiplication_rankLE (K := K) (m ^ 0) (n ^ 0) (p ^ 0))
      simpa only [Nat.zero_mul] using hbase.mono (s := r ^ 0) (by simp)
  | succ k ih =>
      rw [show (k + 1) * d = k * d + d from by ring,
        pow_succ r k, pow_succ m k, pow_succ n k, pow_succ p k]
      exact ih.matrixMultiplication_mul h

end Tensor.BorderRankLEAt

/-! ## From a geometric family of rank bounds to an admissible rectangular exponent -/

/-- Powering the middle-dimension hypothesis: `A^κ ≤ C` implies `(A^k)^κ ≤ C^k`. -/
theorem rpow_pow_le_pow_of_rpow_le {A C : ℕ} {κ : ℝ}
    (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ)) (k : ℕ) :
    (((A ^ k : ℕ) : ℝ)) ^ κ ≤ ((C ^ k : ℕ) : ℝ) := by
  have hA : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hswap : (((A : ℝ)) ^ k) ^ κ = (((A : ℝ)) ^ κ) ^ k := by
    rw [← Real.rpow_natCast ((A : ℝ)) k, ← Real.rpow_natCast (((A : ℝ)) ^ κ) k,
      ← Real.rpow_mul hA, ← Real.rpow_mul hA, mul_comm]
  have hmono : (((A : ℝ)) ^ κ) ^ k ≤ ((C : ℝ)) ^ k := by
    have hnn : (0 : ℝ) ≤ ((A : ℝ)) ^ κ := Real.rpow_nonneg hA κ
    gcongr
  push_cast
  rw [hswap]
  exact hmono

/-- **Rectangular analogue of `matrixExponentLE_of_power_rank_exponentialBound`.**

If the geometric family `⟨A^k, A^k, C^k⟩` — with `A^κ ≤ C`, so that every member is a legitimate
`κ`-rectangular product — admits rank certificates growing at exponential rate `ρ`, then
`log ρ / log A` is an admissible exponent for the `κ`-rectangular rank sequence.

Every scale `n ≥ 1` is covered by `k = Nat.clog A n`: `n ≤ A^k` by `Nat.le_pow_clog`, and the
ceiling `⌈n^κ⌉₊` is at most `C^k` because `n^κ ≤ (A^k)^κ ≤ C^k` and `C^k` is a natural number. -/
theorem rectangularMatrixExponentLE_of_power_rank_exponentialBound
    {A C : ℕ} (hA : 1 < A) {κ : ℝ} (hκ : 0 ≤ κ) (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ))
    {a : ℕ → ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ) (ha : ExponentialBound a ρ)
    (hrank : ∀ k, RankLE (a k)
      (matrixMultiplication (K := K) (A ^ k) (A ^ k) (C ^ k))) :
    RectangularMatrixExponentLE K κ (Real.log ρ / Real.log A) := by
  rcases ha with ⟨_hρnonneg, D, hD, ha⟩
  have hAReal : (1 : ℝ) < A := by exact_mod_cast hA
  have hlogA : 0 < Real.log (A : ℝ) := Real.log_pos hAReal
  refine ⟨div_nonneg (Real.log_nonneg hρ) hlogA.le, D * ρ,
    mul_pos hD (zero_lt_one.trans_le hρ), ?_⟩
  intro n hn
  set k := Nat.clog A n with hk
  have hpow : n ≤ A ^ k := Nat.le_pow_clog hA n
  have hmidk : ((n : ℝ)) ^ κ ≤ ((C ^ k : ℕ) : ℝ) := by
    refine le_trans ?_ (rpow_pow_le_pow_of_rpow_le hmid k)
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hpow) hκ
  have hres : Restricts (matrixMultiplication (K := K) (A ^ k) (A ^ k) (C ^ k))
      (matrixMultiplication (K := K) n n (rectangularMiddleDimension κ n)) :=
    matrixMultiplication_restricts hpow hpow (Nat.ceil_le.mpr hmidk)
  have hrankn : rectangularMatrixRankSequence K κ n ≤ a k := by
    rw [rectangularMatrixRankSequence_eq_rank_outer]
    exact le_trans (rank_restricts_le hres) (rank_le_iff.mpr (hrank k))
  have hclog : ρ ^ k ≤ ρ * (n : ℝ) ^ (Real.log ρ / Real.log A) :=
    real_pow_clog_le_mul_rpow hA hρ hn
  calc
    (rectangularMatrixRankSequence K κ n : ℝ) ≤ (a k : ℝ) := by exact_mod_cast hrankn
    _ ≤ D * ρ ^ k := ha k
    _ ≤ D * (ρ * (n : ℝ) ^ (Real.log ρ / Real.log A)) :=
      mul_le_mul_of_nonneg_left hclog hD.le
    _ = (D * ρ) * (n : ℝ) ^ (Real.log ρ / Real.log A) := by ring

/-! ## Bini's theorem, rectangular form -/

/-- **Bini's interpolation principle for the rectangular exponent, degree-aware form.**

A single constructive border-rank-`r` certificate for the rectangular product `⟨A, A, C⟩` whose
outer dimension dominates `A^κ` proves `ω(1, 1, κ) ≤ log r / log A`.

The polynomial interpolation cost `(k·d + 1)^3` incurred when the `k`-th power of the certificate
is turned into an ordinary rank certificate is absorbed exactly as in the square case: it is
subexponential, so it fits inside the arbitrarily small exponential slack
`ρ = r·exp(ε·log A)`. -/
theorem rectangularOmega_le_log_of_borderRankLEAt {A C r d : ℕ} {κ : ℝ}
    (hA : 1 < A) (hr : 1 ≤ r) (hκ : 0 ≤ κ) (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ))
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) A A C)) :
    rectangularOmega K κ ≤ Real.log r / Real.log A := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hAReal : (1 : ℝ) < A := by exact_mod_cast hA
  have hlogA : 0 < Real.log (A : ℝ) := Real.log_pos hAReal
  have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrPos : (0 : ℝ) < r := zero_lt_one.trans_le hrReal
  let ρ : ℝ := (r : ℝ) * Real.exp (ε * Real.log A)
  have hexp : 1 < Real.exp (ε * Real.log A) :=
    Real.one_lt_exp_iff.mpr (mul_pos hε hlogA)
  have hrρ : (r : ℝ) < ρ := by
    dsimp [ρ]
    nlinarith [mul_lt_mul_of_pos_left hexp hrPos]
  have hρone : 1 ≤ ρ := hrReal.trans hrρ.le
  let a : ℕ → ℕ := fun k ↦ r ^ k * (k * d + 1) ^ 3
  have ha : ExponentialBound a ρ :=
    ExponentialBound.of_le_pow_mul_affine hrρ (fun k ↦ le_rfl)
  have hrank : ∀ k, RankLE (a k)
      (matrixMultiplication (K := K) (A ^ k) (A ^ k) (C ^ k)) := by
    intro k
    exact (h.matrixMultiplication_pow_general k).toRankLE
  have homega := rectangularOmega_le K
    (rectangularMatrixExponentLE_of_power_rank_exponentialBound
      (K := K) hA hκ hmid hρone ha hrank)
  have hlogρ : Real.log ρ = Real.log r + ε * Real.log A := by
    dsimp [ρ]
    rw [Real.log_mul hrPos.ne' (Real.exp_ne_zero _), Real.log_exp]
  rw [hlogρ] at homega
  calc
    rectangularOmega K κ ≤ (Real.log r + ε * Real.log A) / Real.log A := homega
    _ = Real.log r / Real.log A + ε := by field_simp

/-- **Bini's interpolation principle for the rectangular exponent.**  Certificate-facing form:
one border-rank-`r` algorithm for `⟨A, A, C⟩` with `A^κ ≤ C` bounds `ω(1, 1, κ)` by
`log r / log A`. -/
theorem rectangularOmega_le_log_of_borderRankLE {A C r : ℕ} {κ : ℝ}
    (hA : 1 < A) (hr : 1 ≤ r) (hκ : 0 ≤ κ) (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ))
    (h : BorderRankLE r (matrixMultiplication (K := K) A A C)) :
    rectangularOmega K κ ≤ Real.log r / Real.log A := by
  rcases h.exists_at with ⟨d, hd⟩
  exact rectangularOmega_le_log_of_borderRankLEAt hA hr hκ hmid hd

/-- Multiplicative form of the rectangular Bini bound: `A ^ ω(1,1,κ) ≤ r`. -/
theorem rpow_rectangularOmega_le_of_borderRankLE {A C r : ℕ} {κ : ℝ}
    (hA : 1 < A) (hr : 1 ≤ r) (hκ : 0 ≤ κ) (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ))
    (h : BorderRankLE r (matrixMultiplication (K := K) A A C)) :
    ((A : ℝ)) ^ (rectangularOmega K κ) ≤ (r : ℝ) := by
  have hAReal : (1 : ℝ) < A := by exact_mod_cast hA
  have hlogA : 0 < Real.log (A : ℝ) := Real.log_pos hAReal
  have hle := rectangularOmega_le_log_of_borderRankLE (K := K) hA hr hκ hmid h
  have hlog : rectangularOmega K κ * Real.log (A : ℝ) ≤ Real.log r :=
    (le_div_iff₀ hlogA).mp hle
  have hrPos : (0 : ℝ) < r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hexp : ((A : ℝ)) ^ (rectangularOmega K κ) =
      Real.exp (rectangularOmega K κ * Real.log (A : ℝ)) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hAReal), mul_comm]
  rw [hexp]
  calc
    Real.exp (rectangularOmega K κ * Real.log (A : ℝ)) ≤ Real.exp (Real.log (r : ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ = (r : ℝ) := Real.exp_log hrPos

end AlgebraicComplexity
