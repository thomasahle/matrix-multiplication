/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Exponent
import AlgebraicComplexity.Tensor.PolynomialInterpolation

/-!
# Border-rank algorithms and the matrix-multiplication exponent

This module packages Bini's interpolation principle for matrix multiplication.  A polynomial
border-rank certificate is powered with its leading degree retained, its leading coefficient is
expanded into ordinary pure tensors, and the resulting polynomial overhead is absorbed in the
definition of `omega`.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

variable {K : Type u} [CommSemiring K]

namespace Tensor.BorderRankLEAt

/-- Degree-aware border certificates multiply under the canonical matrix-multiplication
reindexing. -/
theorem matrixMultiplication_mul
    {m n p m' n' p' r s d e : ℕ}
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) m n p))
    (h' : BorderRankLEAt s e (matrixMultiplication (K := K) m' n' p')) :
    BorderRankLEAt (r * s) (d + e)
      (matrixMultiplication (K := K) (m * m') (n * n') (p * p')) := by
  have hproduct := (h.external h').map
    (fun c ↦ (mmProductLegEquiv (K := K) m n p m' n' p' c).toLinearMap)
  rw [← mmExternalEquiv_matrixMultiplication]
  simpa [mmExternalEquiv, PiTensorProduct.congr] using hproduct

/-- Powering a square degree-aware border certificate multiplies its size and adds its degree. -/
theorem matrixMultiplication_pow {q r d : ℕ}
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) q q q)) (k : ℕ) :
    BorderRankLEAt (r ^ k) (k * d)
      (matrixMultiplication (K := K) (q ^ k) (q ^ k) (q ^ k)) := by
  induction k with
  | zero =>
      have hbase : BorderRankLEAt (q ^ 0 * q ^ 0 * q ^ 0) 0
          (matrixMultiplication (K := K) (q ^ 0) (q ^ 0) (q ^ 0)) :=
        RankLE.toBorderRankLEAt
          (matrixMultiplication_rankLE (K := K) (q ^ 0) (q ^ 0) (q ^ 0))
      simpa only [Nat.zero_mul] using hbase.mono (s := r ^ 0) (by simp)
  | succ k ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.matrixMultiplication_mul h

end Tensor.BorderRankLEAt

/-- An exponential rank bound on all `q`-power dimensions gives the corresponding polynomial
matrix-multiplication bound on arbitrary dimensions. -/
theorem matrixExponentLE_of_power_rank_exponentialBound
    {q : ℕ} (hq : 1 < q) {a : ℕ → ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ)
    (ha : ExponentialBound a ρ)
    (hrank : ∀ k, RankLE (a k)
      (matrixMultiplication (K := K) (q ^ k) (q ^ k) (q ^ k))) :
    MatrixExponentLE K (Real.log ρ / Real.log q) := by
  rcases ha with ⟨hρnonneg, C, hC, ha⟩
  have hqReal : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqReal
  refine ⟨div_nonneg (Real.log_nonneg hρ) hlogq.le,
    C * ρ, mul_pos hC (zero_lt_one.trans_le hρ), ?_⟩
  intro n hn
  let k := Nat.clog q n
  have hnRank : squareMatrixRankSequence K n ≤ a k := by
    apply rank_le_iff.mpr
    exact (hrank k).of_restricts
      (matrixMultiplication_restricts
        (Nat.le_pow_clog hq n) (Nat.le_pow_clog hq n) (Nat.le_pow_clog hq n))
  have hclog : ρ ^ k ≤ ρ * (n : ℝ) ^ (Real.log ρ / Real.log q) := by
    exact real_pow_clog_le_mul_rpow hq hρ hn
  calc
    (squareMatrixRankSequence K n : ℝ) ≤ (a k : ℝ) := by exact_mod_cast hnRank
    _ ≤ C * ρ ^ k := ha k
    _ ≤ C * (ρ * (n : ℝ) ^ (Real.log ρ / Real.log q)) :=
      mul_le_mul_of_nonneg_left hclog hC.le
    _ = (C * ρ) * (n : ℝ) ^ (Real.log ρ / Real.log q) := by ring

/-- Degree-aware form of Bini's theorem: a border-rank-`r` algorithm for `q × q`
multiplication gives `omega ≤ log(r) / log(q)`. -/
theorem omega_le_log_of_borderRankLEAt {q r d : ℕ}
    (hq : 1 < q) (hr : 1 ≤ r)
    (h : BorderRankLEAt r d (matrixMultiplication (K := K) q q q)) :
    omega K ≤ Real.log r / Real.log q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hqReal : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqReal
  have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrPos : (0 : ℝ) < r := zero_lt_one.trans_le hrReal
  let ρ : ℝ := (r : ℝ) * Real.exp (ε * Real.log q)
  have hexp : 1 < Real.exp (ε * Real.log q) :=
    Real.one_lt_exp_iff.mpr (mul_pos hε hlogq)
  have hrρ : (r : ℝ) < ρ := by
    dsimp [ρ]
    nlinarith [mul_lt_mul_of_pos_left hexp hrPos]
  have hρone : 1 ≤ ρ := hrReal.trans hrρ.le
  let a : ℕ → ℕ := fun k ↦ r ^ k * (k * d + 1) ^ 3
  have ha : ExponentialBound a ρ := by
    exact ExponentialBound.of_le_pow_mul_affine hrρ (fun k ↦ le_rfl)
  have hrank : ∀ k, RankLE (a k)
      (matrixMultiplication (K := K) (q ^ k) (q ^ k) (q ^ k)) := by
    intro k
    exact (h.matrixMultiplication_pow k).toRankLE
  have homega := matrixMultiplicationExponent_le K
    (matrixExponentLE_of_power_rank_exponentialBound (K := K) hq hρone ha hrank)
  have hlogρ : Real.log ρ = Real.log r + ε * Real.log q := by
    dsimp [ρ]
    rw [Real.log_mul (by exact_mod_cast hrPos.ne') (Real.exp_ne_zero _), Real.log_exp]
  rw [hlogρ] at homega
  calc
    omega K ≤ (Real.log r + ε * Real.log q) / Real.log q := homega
    _ = Real.log r / Real.log q + ε := by field_simp

/-- Certificate-facing form of Bini's theorem. -/
theorem omega_le_log_of_borderRankLE {q r : ℕ}
    (hq : 1 < q) (hr : 1 ≤ r)
    (h : BorderRankLE r (matrixMultiplication (K := K) q q q)) :
    omega K ≤ Real.log r / Real.log q := by
  rcases h.exists_at with ⟨d, hd⟩
  exact omega_le_log_of_borderRankLEAt hq hr hd

end AlgebraicComplexity
