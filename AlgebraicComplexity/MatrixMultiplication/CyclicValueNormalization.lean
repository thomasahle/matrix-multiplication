/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicValue
import AlgebraicComplexity.MatrixMultiplication.TauValueCore

/-!
# Normalization identities for cyclic value certificates

This module contains numerical identities shared by cyclic restriction and degeneration clients.
They depend only on the positive finite dimension data stored in
`CyclicExtractionCertificate`; the semantic extraction relation is completely arbitrary.

The principal identity says that raising the normalized cyclic term

`(∑ᵢ volumeᵢ^τ)^(1/(3k))`

to the real exponent `3k` recovers the unnormalized volume sum.  This is the bridge needed when a
cyclic leaf is inserted into a larger, differently normalized value assembly.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {T : Tensor3 K V} {τ : ℝ}
variable {Rel : CyclicExtractionRelation K T}

/-- Raising a cyclic certificate term to `3·power` exactly cancels its normalization.

Proof sketch: the matrix-volume sum is positive, so real-power multiplication is valid.  The
positive source power makes `3·power` nonzero, and its inverse cancels. -/
theorem CyclicExtractionCertificate.term_rpow_three_mul_power
    (certificate : CyclicExtractionCertificate K T τ Rel) :
    certificate.term ^ (((3 * certificate.power : ℕ) : ℝ)) =
      matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize τ := by
  have hsum : 0 < matrixMultiplicationVolumePowerSum
      certificate.xSize certificate.ySize certificate.zSize τ :=
    matrixMultiplicationVolumePowerSum_pos certificate.copies_pos
      certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos τ
  have hthreePower : 3 * certificate.power ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) certificate.power_pos.ne'
  have hthreePowerReal : ((3 * certificate.power : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hthreePower
  unfold CyclicExtractionCertificate.term cyclicValueTerm
  rw [← Real.rpow_mul hsum.le, inv_mul_cancel₀ hthreePowerReal, Real.rpow_one]

/-- A lower bound on a normalized cyclic term yields the corresponding powered lower bound on
the unnormalized matrix-volume sum. -/
theorem CyclicExtractionCertificate.rpow_three_mul_power_le_volumePowerSum
    (certificate : CyclicExtractionCertificate K T τ Rel)
    {W : ℝ} (hW : 0 ≤ W) (hle : W ≤ certificate.term) :
    W ^ (((3 * certificate.power : ℕ) : ℝ)) ≤
      matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize τ := by
  rw [← certificate.term_rpow_three_mul_power K]
  exact Real.rpow_le_rpow hW hle (by positivity)

end AlgebraicComplexity
