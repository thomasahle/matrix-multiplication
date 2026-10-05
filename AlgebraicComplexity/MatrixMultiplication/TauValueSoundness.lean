/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import AlgebraicComplexity.MatrixMultiplication.TauValueCore
import AlgebraicComplexity.Tensor.AsymptoticRank

/-!
# Soundness of the Coppersmith--Winograd τ-value

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`). This module connects the finite
certificates of `TauValueCore.lean` to asymptotic rank and the matrix-multiplication exponent.
It is the analytic half of the value API; finite extraction and assembly clients should import
`TauValueCore` instead.

## Mathematical content

Schönhage's asymptotic sum inequality bounds the `ω/3`-volume sum of every extracted direct sum
by the asymptotic rank of its source. Taking the certificate's `N`th root gives

`certificate.term (omega F / 3) ≤ Tensor.asymptoticRank T`.

Consequently, if a certificate at exponent `τ` has term strictly larger than a known asymptotic-
or border-rank bound, then `omega F < 3 * τ`. The strict hypothesis is essential: the analogous
non-strict implication is false already for `⟨1,1,1⟩`.

## Principal results

* `TauValueCertificate.term_le_asymptoticRank` is certificate-level Schönhage soundness.
* `tauValueValues_bddAbove` proves boundedness of the supremum-level value set when
  `τ ≤ omega F / 3`.
* `omega_lt_three_mul_of_certificate` and its border-rank, supremum, and approximate-sequence
  corollaries turn strict value bounds into exponent bounds.
* `omega_le_log_seven_div_log_two_of_tauValue_borderRankLE` is the Strassen direction
  regression.

The companion `TauValueCyclicSoundness.lean` adapts symmetrized cyclic certificates to these
ordinary theorems.  It is separate so ordinary value clients do not import cyclic tensor products
or their border-rank calculus.

The finite definitions remain usable over a commutative semiring; this soundness layer assumes a
field exactly where Schönhage's theorem and `omega` do.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## The value-to-exponent theorem -/

section Soundness

variable (F : Type u) [Field F]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

/-- **Schönhage's inequality applied to one value certificate.**  The `ω/3`-weight of the
extracted family is bounded by the asymptotic rank of the degenerated power. -/
theorem TauValueCertificate.volumePowerSum_le_asymptoticRank_power {T : Tensor3 F V}
    (certificate : TauValueCertificate F T) :
    matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize certificate.zSize
        (omega F / 3) ≤
      Tensor.asymptoticRank (Tensor.power T certificate.power) := by
  have hschonhage := asymptoticSumInequality F (Fin certificate.copies)
    (PowerSpace F V certificate.power) (Tensor.power T certificate.power)
    certificate.xSize certificate.ySize certificate.zSize
    certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos certificate.degenerates
  simpa [asymptoticSum] using hschonhage

/-- **`V_{ω/3}(T) ≤ R̃(T)`, certificate by certificate.**  This is the soundness half of the value
formalism: no finite extraction can be worth more at the exponent `ω/3` than the asymptotic rank of
its source.  It is the only statement in this module that consumes
`AlgebraicComplexity.asymptoticSumInequality`.

Proof sketch: the previous lemma bounds the weight sum by `R̃(T^{⊗N})`, submultiplicativity of
asymptotic rank along powers bounds that by `R̃(T)^N`, and taking `N`th roots is
`Real.pow_rpow_inv_natCast`. -/
theorem TauValueCertificate.term_le_asymptoticRank {T : Tensor3 F V}
    (certificate : TauValueCertificate F T) :
    certificate.term (omega F / 3) ≤ Tensor.asymptoticRank T := by
  have hsum := certificate.volumePowerSum_le_asymptoticRank_power (F := F)
  have hpow : Tensor.asymptoticRank (Tensor.power T certificate.power) ≤
      Tensor.asymptoticRank T ^ certificate.power :=
    Tensor.asymptoticRank_power_le T certificate.power
  have hnonneg : (0 : ℝ) ≤ matrixMultiplicationVolumePowerSum
      certificate.xSize certificate.ySize certificate.zSize (omega F / 3) :=
    le_of_lt (matrixMultiplicationVolumePowerSum_pos certificate.copies_pos
      certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos _)
  have hexp : (0 : ℝ) ≤ ((certificate.power : ℕ) : ℝ)⁻¹ := by positivity
  have hroot : certificate.term (omega F / 3) ≤
      (Tensor.asymptoticRank T ^ certificate.power) ^ ((certificate.power : ℝ)⁻¹) :=
    Real.rpow_le_rpow hnonneg (hsum.trans hpow) hexp
  rwa [Real.pow_rpow_inv_natCast (Tensor.asymptoticRank_nonneg T)
    (certificate.power_pos.ne')] at hroot

/-- **The value set is bounded above by the asymptotic rank for every `τ ≤ ω/3`.**

This is the generic boundedness statement that makes `tauValue` a genuine supremum in the regime
the classical theory uses; nothing is claimed for `τ > ω/3`. -/
theorem tauValueValues_bddAbove {T : Tensor3 F V} {τ : ℝ} (hτ : τ ≤ omega F / 3) :
    BddAbove (tauValueValues F T τ) := by
  refine ⟨Tensor.asymptoticRank T, ?_⟩
  rintro x ⟨certificate, rfl⟩
  exact (certificate.term_mono hτ).trans (certificate.term_le_asymptoticRank (F := F))

/-- **The value-to-exponent theorem** (`[CoppersmithWinograd1990]`, §8, p. 264).

If the asymptotic rank of `T` is at most `r` and some value certificate of `T` is worth strictly
more than `r` at the exponent `τ`, then `ω < 3τ`.

This is CW90's auxiliary-equation step made precise.  Their display
`(q+2)^{2N} ≥ N^{-p} · (weight of the surviving triples)` compares exactly these two quantities;
the strict inequality is what their optimization supplies, and, as explained in the module
docstring, the non-strict version of the statement is false.

Proof sketch: if `3τ ≤ ω` then `τ ≤ ω/3`, so the certificate is worth at least as much at `ω/3`
as at `τ` (`term_mono`, using that every matrix volume is at least one), and
`term_le_asymptoticRank` bounds the former by `r`. -/
theorem omega_lt_three_mul_of_certificate {T : Tensor3 F V} {r τ : ℝ}
    (hrank : Tensor.asymptoticRank T ≤ r) (certificate : TauValueCertificate F T)
    (hterm : r < certificate.term τ) :
    omega F < 3 * τ := by
  by_contra hcontra
  have hcontra' : 3 * τ ≤ omega F := not_lt.mp hcontra
  have hτ : τ ≤ omega F / 3 := by linarith
  have hmono := certificate.term_mono hτ
  have hsound := certificate.term_le_asymptoticRank (F := F)
  linarith

/-- The non-strict conclusion, for clients that only need `ω ≤ 3τ`. -/
theorem omega_le_three_mul_of_certificate {T : Tensor3 F V} {r τ : ℝ}
    (hrank : Tensor.asymptoticRank T ≤ r) (certificate : TauValueCertificate F T)
    (hterm : r < certificate.term τ) :
    omega F ≤ 3 * τ :=
  le_of_lt (omega_lt_three_mul_of_certificate F hrank certificate hterm)

/-- **The value-to-exponent theorem with a constructive border-rank premise.**  A border-rank
certificate is the convenient hypothesis for Coppersmith--Winograd clients, since it is exactly
what their approximate algorithms exhibit. -/
theorem omega_lt_three_mul_of_borderRankLE {T : Tensor3 F V} {b : ℕ} {τ : ℝ}
    (hborder : BorderRankLE b T) (certificate : TauValueCertificate F T)
    (hterm : (b : ℝ) < certificate.term τ) :
    omega F < 3 * τ := by
  refine omega_lt_three_mul_of_certificate F ?_ certificate hterm
  refine (Tensor.asymptoticRank_le_borderRank T).trans ?_
  exact_mod_cast Tensor.borderRank_le_iff.mpr hborder

/-- **The value-to-exponent theorem read from the supremum.**  If `r` is strictly below `V_τ(T)`
and bounds the asymptotic rank of `T`, then `ω < 3τ`.

Proof sketch: `exists_lt_of_lt_csSup` extracts one certificate above `r`. -/
theorem omega_lt_three_mul_of_lt_tauValue {T : Tensor3 F V} {r τ : ℝ}
    (hrank : Tensor.asymptoticRank T ≤ r)
    (hnonempty : (tauValueValues F T τ).Nonempty) (hvalue : r < tauValue F T τ) :
    omega F < 3 * τ := by
  obtain ⟨x, ⟨certificate, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hnonempty hvalue
  exact omega_lt_three_mul_of_certificate F hrank certificate hx

/-- **The `ε`-robust form of the value-to-exponent theorem.**  A sequence of certificates whose
weights approach `v` from below suffices; no supremum, limit, or attainment is needed.

This is the shape produced by subexponential-loss laser analyses, which construct, for each
`ε > 0`, a finite certificate of weight at least `v − ε`. -/
theorem omega_lt_three_mul_of_approximate_certificates {T : Tensor3 F V} {r v τ : ℝ}
    (hrank : Tensor.asymptoticRank T ≤ r) (hrv : r < v)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ certificate : TauValueCertificate F T,
      v - ε ≤ certificate.term τ) :
    omega F < 3 * τ := by
  obtain ⟨certificate, hcert⟩ := happrox ((v - r) / 2) (by linarith)
  refine omega_lt_three_mul_of_certificate F hrank certificate ?_
  linarith

end Soundness


/-! ## Regression client: `ω ≤ log 7 / log 2` as a value statement -/

section StrassenRegression

variable (F : Type u) [Field F]

/-- **The Strassen regression instance, phrased through the value calculus.**

A border-rank-seven certificate for `⟨2,2,2⟩` gives, for every `τ` with `8^τ > 7`, the value
certificate of weight `8^τ` and hence `ω < 3τ`; letting `τ` decrease to `log_8 7` yields
`ω ≤ 3 · log_8 7 = log₂ 7`.  The conclusion agrees in value and direction with
`AlgebraicComplexity.omega_le_log_of_rankLE` and with
`AlgebraicComplexity.omega_le_log_two_seven_of_borderRankLE` from the galactic-method client, so
the value route is checked against the two existing routes.

The premise is stated as a hypothesis rather than imported: `⟨2,2,2⟩`'s rank-seven decomposition
is a layer-4 client, and this layer must not depend on it. -/
theorem omega_le_log_seven_div_log_two_of_tauValue_borderRankLE
    (hborder : BorderRankLE 7 (AlgebraicComplexity.matrixMultiplication (K := F) 2 2 2)) :
    omega F ≤ Real.log 7 / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog8ne : Real.log 8 ≠ 0 := by rw [hlog8]; positivity
  have hroot : (8 : ℝ) ^ (Real.log 7 / Real.log 8) = 7 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 8)]
    have hcollapse : Real.log 8 * (Real.log 7 / Real.log 8) = Real.log 7 := by
      field_simp
    rw [hcollapse, Real.exp_log (by norm_num)]
  have hvalue : 3 * (Real.log 7 / Real.log 8) = Real.log 7 / Real.log 2 := by
    rw [hlog8]
    field_simp
  by_contra hcontra
  have hgap : Real.log 7 / Real.log 2 < omega F := not_le.mp hcontra
  set ε : ℝ := (omega F - Real.log 7 / Real.log 2) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hstep : omega F < 3 * (Real.log 7 / Real.log 8 + ε / 3) := by
    refine omega_lt_three_mul_of_borderRankLE F hborder
      (TauValueCertificate.matrixMultiplication F (a := 2) (b := 2) (c := 2)
        (by norm_num) (by norm_num) (by norm_num)) ?_
    rw [TauValueCertificate.term_matrixMultiplication]
    have hcast : (((2 * 2 * 2 : ℕ) : ℝ)) = (8 : ℝ) := by norm_num
    rw [hcast]
    have hlt : (8 : ℝ) ^ (Real.log 7 / Real.log 8) <
        (8 : ℝ) ^ (Real.log 7 / Real.log 8 + ε / 3) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [hroot] at hlt
    calc (((7 : ℕ)) : ℝ) = (7 : ℝ) := by norm_num
      _ < (8 : ℝ) ^ (Real.log 7 / Real.log 8 + ε / 3) := hlt
  have hexpand : 3 * (Real.log 7 / Real.log 8 + ε / 3) = Real.log 7 / Real.log 2 + ε := by
    rw [← hvalue]; ring
  rw [hexpand] at hstep
  rw [hε] at hstep
  linarith

end StrassenRegression

end AlgebraicComplexity
