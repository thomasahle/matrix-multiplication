/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Matrix-multiplication volumes

This leaf defines the numerical volume of a rectangular matrix-multiplication tensor and finite
power sums of those volumes.  It contains no tensor-space or exponent machinery, so both finite
value certificates and analytic asymptotic modules can share the definitions without importing
one another.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι]

/-- Volume of the matrix-multiplication tensor indexed by `i`. -/
def matrixMultiplicationVolume (m n p : ι → ℕ) (i : ι) : ℕ :=
  m i * n i * p i

/-- The finite volume power sum used by value and asymptotic-sum certificates. -/
noncomputable def matrixMultiplicationVolumePowerSum
    (m n p : ι → ℕ) (τ : ℝ) : ℝ :=
  ∑ i, (matrixMultiplicationVolume m n p i : ℝ) ^ τ

/-- A constant family of `F` equally sized matrix-multiplication tensors contributes `F` times
one volume power.

This elementary normalization lemma is useful for finite value certificates extracted by hashing,
whose surviving blocks all have the same dimensions. -/
theorem matrixMultiplicationVolumePowerSum_const
    (F m n p : ℕ) (τ : ℝ) :
    matrixMultiplicationVolumePowerSum
        (fun _ : Fin F ↦ m) (fun _ : Fin F ↦ n) (fun _ : Fin F ↦ p) τ =
      (F : ℝ) * ((m * n * p : ℕ) : ℝ) ^ τ := by
  unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]

/-- **Constant-volume cyclic lower terms are invariant under proportional repetition.**

Suppose one repetition has copy lower bound `W`, matrix dimensions `m`, `n`, `p`, and source
length `N`.  Repeating it `k` times replaces these by `W ^ k`, `m ^ k`, `n ^ k`, `p ^ k`, and
`N * k`.  After the cyclic normalization by `1 / (3 * N * k)`, the resulting real value is
exactly the one-repetition value.

This is a purely numerical lemma.  In particular, clients may obtain their finite family by any
restriction or degeneration; no zeroing operation is built into the statement.

Proof sketch: the product of the three repeated dimensions is the `k`th power of the original
volume.  Real-power multiplication then turns the entire base into a `k`th power, and `k`
cancels against the proportional source length. -/
theorem normalizedConstantVolumePower_eq
    (W τ : ℝ) (m n p N k : ℕ)
    (hW : 0 < W) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (hN : 0 < N) (hk : 0 < k) :
    ((W ^ k) * (((m ^ k * n ^ k * p ^ k : ℕ) : ℝ) ^ τ)) ^
        (((3 * (N * k) : ℕ) : ℝ)⁻¹) =
      (W * (((m * n * p : ℕ) : ℝ) ^ τ)) ^
        (((3 * N : ℕ) : ℝ)⁻¹) := by
  let volume : ℕ := m * n * p
  have hvolumeNat : 0 < volume := Nat.mul_pos (Nat.mul_pos hm hn) hp
  have hvolume : (0 : ℝ) < (volume : ℕ) := by exact_mod_cast hvolumeNat
  have hbase : 0 < W * ((volume : ℝ) ^ τ) :=
    mul_pos hW (Real.rpow_pos_of_pos hvolume τ)
  have hdimensions :
      (((m ^ k * n ^ k * p ^ k : ℕ) : ℝ) ^ τ) =
        (((volume : ℕ) : ℝ) ^ τ) ^ k := by
    have hnat : m ^ k * n ^ k * p ^ k = volume ^ k := by
      simp only [volume, mul_pow]
    rw [hnat, Nat.cast_pow]
    exact (Real.rpow_pow_comm (Nat.cast_nonneg volume) τ k).symm
  rw [hdimensions, ← mul_pow]
  change ((W * ((volume : ℝ) ^ τ)) ^ k) ^
      (((3 * (N * k) : ℕ) : ℝ)⁻¹) =
    (W * ((volume : ℝ) ^ τ)) ^ (((3 * N : ℕ) : ℝ)⁻¹)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
  congr 1
  push_cast
  field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast hk.ne',
    show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']

end AlgebraicComplexity
