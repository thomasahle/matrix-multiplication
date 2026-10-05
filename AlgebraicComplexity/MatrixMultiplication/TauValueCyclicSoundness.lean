/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicValueTensor
import AlgebraicComplexity.MatrixMultiplication.TauValueSoundness

/-!
# Cyclic certificates as ordinary `τ`-value certificates

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`). This module is the explicit adapter from
the repository's symmetrized three-orientation degeneration certificates to the ordinary
Coppersmith--Winograd value soundness theorem.

A cyclic certificate for `T` is interpreted as a length-one ordinary value certificate for its
three-orientation source. The source border-rank bound is raised to the corresponding `3k`th
power, and ordinary certificate soundness then yields `omega < 3 * τ`.

Keeping this bridge separate means users of ordinary `TauValueCertificate`s do not import cyclic
tensor products or their border-rank calculus. The compatibility umbrella `TauValue.lean`
continues to re-export both APIs.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v

/-! ## The bridge to the symmetrized cyclic certificates -/

section CyclicBridge

variable (F : Type u) [Field F]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

/-- A cyclic degeneration certificate of `T` is a length-one value certificate of the
three-orientation source `T^{⊗k} ⊗ (T^{⊗k})^π ⊗ (T^{⊗k})^{π²}`. -/
noncomputable def CyclicDegenerationCertificate.toTauValueCertificate {T : Tensor3 F V} {τ : ℝ}
    (certificate : CyclicDegenerationCertificate F T τ) :
    TauValueCertificate F (cyclicPowerProduct F T certificate.power) where
  power := 1
  copies := certificate.copies
  xSize := certificate.xSize
  ySize := certificate.ySize
  zSize := certificate.zSize
  power_pos := Nat.one_pos
  copies_pos := certificate.copies_pos
  xSize_pos := certificate.xSize_pos
  ySize_pos := certificate.ySize_pos
  zSize_pos := certificate.zSize_pos
  degenerates :=
    (PolynomialDegenerates.of_restricts
      (Isomorphic.power_one (cyclicPowerProduct F T certificate.power)).restricts).trans
      certificate.degenerates

/-- **The value-to-exponent theorem for the repository's symmetrized cyclic certificates.**

If `T` has border rank at most `b` and a polynomial-degeneration cyclic value certificate at
exponent `τ` whose normalized weight `(∑_h (m_h n_h p_h)^τ)^{1/(3k)}` strictly exceeds `b`, then
`ω < 3τ`.

This is the plug-in form for laser clients: `CyclicDegenerationCertificate` (and, through
`CyclicValueCertificate.toDegeneration`, the exact-restriction certificates as well) is exactly
what `MatrixMultiplication/CyclicValueTensor.lean` and its hashing clients construct.

Proof sketch: the certificate is a length-one value certificate of the three-orientation source,
whose border rank is at most `b^{3k}` (`borderRank_cyclicPowerProduct_le`).  Raising the
hypothesis `b < (∑ …)^{1/(3k)}` to the power `3k` turns it into `b^{3k} < ∑ …`, which is the
strict hypothesis of `omega_lt_three_mul_of_certificate`. -/
theorem omega_lt_three_mul_of_cyclicDegenerationCertificate {T : Tensor3 F V} {τ : ℝ} {b : ℕ}
    (hborder : Tensor.borderRank T ≤ b)
    (certificate : CyclicDegenerationCertificate F T τ)
    (hterm : (b : ℝ) < certificate.term) :
    omega F < 3 * τ := by
  have hkpos : 0 < certificate.power := certificate.power_pos
  have h3k : 3 * certificate.power ≠ 0 := by omega
  have h3kR : ((3 * certificate.power : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h3k
  have h3kpos : (0 : ℝ) < ((3 * certificate.power : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero h3k
  have hSpos : 0 < matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
      certificate.zSize τ :=
    matrixMultiplicationVolumePowerSum_pos certificate.copies_pos certificate.xSize_pos
      certificate.ySize_pos certificate.zSize_pos τ
  have hterm' : (b : ℝ) < (matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
      certificate.zSize τ) ^ (((3 * certificate.power : ℕ) : ℝ))⁻¹ := hterm
  have hcancel : ((matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
        certificate.zSize τ) ^ (((3 * certificate.power : ℕ) : ℝ))⁻¹) ^
        (((3 * certificate.power : ℕ) : ℝ)) =
      matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize certificate.zSize τ := by
    rw [← Real.rpow_mul hSpos.le, inv_mul_cancel₀ h3kR, Real.rpow_one]
  -- Raise the strict inequality to the power `3k`.
  have hstrict : ((b : ℝ)) ^ (((3 * certificate.power : ℕ) : ℝ)) <
      matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
        certificate.zSize τ := by
    rw [← hcancel]
    exact Real.rpow_lt_rpow (Nat.cast_nonneg b) hterm' h3kpos
  -- The three-orientation source has asymptotic rank at most `b ^ (3k)`.
  have hrank : Tensor.asymptoticRank (cyclicPowerProduct F T certificate.power) ≤
      ((b : ℝ)) ^ (3 * certificate.power) := by
    refine (Tensor.asymptoticRank_le_borderRank _).trans ?_
    have hnat : Tensor.borderRank (cyclicPowerProduct F T certificate.power) ≤
        b ^ (3 * certificate.power) :=
      (borderRank_cyclicPowerProduct_le F T certificate.power).trans
        (Nat.pow_le_pow_left hborder (3 * certificate.power))
    exact_mod_cast hnat
  refine omega_lt_three_mul_of_certificate F hrank certificate.toTauValueCertificate ?_
  show ((b : ℝ)) ^ (3 * certificate.power) <
    tauValueTerm τ 1 certificate.xSize certificate.ySize certificate.zSize
  rw [tauValueTerm, Nat.cast_one, inv_one, Real.rpow_one, ← Real.rpow_natCast (b : ℝ)]
  exact hstrict

end CyclicBridge

end AlgebraicComplexity

