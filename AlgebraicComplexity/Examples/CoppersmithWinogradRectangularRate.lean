/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.RpowInequalities
import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularHashing
import AlgebraicComplexity.MatrixMultiplication.RectangularSchedule

/-!
# The rectangular full-CW rate inequality

This module instantiates the Huang--Pan schedule of
`MatrixMultiplication/RectangularSchedule.lean` -- `(a, b, e, f) = (pN, mN, uN, vN)`, `N → ∞` --
on the rectangular extraction of `Examples/CoppersmithWinogradRectangularHashing.lean`, ending at
the single scalar inequality

`(E₀ / Φ) · q ^ (m · ω(1,1,p/m)) ≤ (q+2) ^ (p + 2m + 2u + v)`,

where

`E₀ = cwRectEntropyBase p m u v = T^T / (p^p · m^{2m} · u^{2u} · v^v)`, `T = p + 2m + 2u + v`,

is the six-fold multinomial growth rate of the selected type and `Φ` is *any* geometric envelope
of the hashing competitor count along the schedule, i.e. any real with

`cwRectTypedFiberBound (pN, mN, uN, vN) ≤ Φ ^ N   for all N`

(`cwRect_master_inequality_of_fiberGrowth`).  The competitor count is Huang--Pan's `M` of
[HP98, p. 276].

Keeping `Φ` a parameter is what lets one schedule serve both branches of [HP98, Section 7]: their
(7.1) instantiates it at the `y`-leg fiber and their (7.2) at the `x`-leg fiber, and the entropy
comparison between the two is never needed inside the schedule.

## What is here and what is in the schedule module

Everything paper-independent -- Bertrand's modulus, Behrend's progression-free set, the
compression bootstrap, the three subexponential losses and their cancellation -- lives in
`MatrixMultiplication/RectangularSchedule.lean` and is shared with the easy-tensor rectangular
tower of `Examples/CoppersmithWinogradEasyRectangularRate.lean`.  This module supplies only the
four instantiating data:

* the extraction, as `cwRect_scheduleExtraction`;
* the entropy base `cwRectEntropyBase` with its loss
  `WordType.proportionalMultinomialLoss (cwRectType p m u v)`;
* the word length `T = p + 2m + 2u + v`, which enters only through the border-rank bound;
* the geometric data `A = q^m`, `C = q^p`, `R = (q+2)^T`.

The three losses removed by the schedule are, in this instance, the Stirling estimate
`cwRectType_entropyBase_pow_le_loss_mul_card` for the six-fold multinomial, the Bertrand/Behrend
hashing loss, and the compression rounding of `exists_compressionScale`.

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299, Sections 5 and 7.1.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Growth

universe u

/-! ## The Huang--Pan schedule constants -/

/-- Huang--Pan's aspect ratio `r = p/m`, as a real number.  The corner parameters `u, v` (their
`L` and `rL`) do not enter it: they change the *rate*, not the shape of the block product.
A tower-local spelling of the shared `AlgebraicComplexity.rectAspectRatio`. -/
noncomputable abbrev cwRectKappa (p m : ℕ) : ℝ := rectAspectRatio p m

/-- The six-fold multinomial growth base of the rectangular type:
`T^T / (p^p · m^{2m} · u^{2u} · v^v)` with `T = p + 2m + 2u + v`. -/
noncomputable def cwRectEntropyBase (p m u v : ℕ) : ℝ :=
  ((p + 2 * m + 2 * u + v : ℕ) : ℝ) ^ (p + 2 * m + 2 * u + v) /
    ((p : ℝ) ^ p * (m : ℝ) ^ (2 * m) * (u : ℝ) ^ (2 * u) * (v : ℝ) ^ v)

theorem cwRectEntropyBase_pos {p m u v : ℕ} (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v) :
    0 < cwRectEntropyBase p m u v := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hsum : (0 : ℝ) < ((p + 2 * m + 2 * u + v : ℕ) : ℝ) := by
    have : 0 < p + 2 * m + 2 * u + v := by omega
    exact_mod_cast this
  unfold cwRectEntropyBase
  positivity

/-- The rectangular constituent really has aspect ratio `κ = p/m`: the outer dimension `q^(pN)`
is exactly the `κ`-th power of the inner dimension `q^(mN)`.  A tower-local spelling of
`AlgebraicComplexity.rectAspectRatio_pow_rpow`. -/
theorem cwRect_rpow_kappa (q p m N : ℕ) (hm : 0 < m) :
    ((q : ℝ) ^ (m * N)) ^ cwRectKappa p m = (q : ℝ) ^ (p * N) :=
  rectAspectRatio_pow_rpow q p m N hm

/-- `κ = p/m` is the value of a positive rational at its numerator and denominator.  A
tower-local spelling of `AlgebraicComplexity.rectAspectRatio_num_den`. -/
theorem cwRectKappa_num_den {r : ℚ} (hr : 0 < r) :
    cwRectKappa r.num.natAbs r.den = (r : ℝ) :=
  rectAspectRatio_num_den hr

/-! ## The extraction, in the shape the schedule consumes -/

section FiniteStep

variable (K : Type u) [Field K]

/-- **The full-CW rectangular extraction as a schedule input.**

At depth `N` the selected type has `(cwRectTypeWords (pN) (mN) (uN) (vN)).card` words and
competitor count `cwRectTypedFiberBound (pN) (mN) (uN) (vN)`, and the extracted constituents are
`⟨(q^m)^N, (q^m)^N, (q^p)^N⟩` inside a tensor of border rank `((q+2)^T)^N`, `T = p+2m+2u+v`.

Presenting the extraction over abstract geometric `(A, C, R)` rather than over the hard-coded
`q^(mN)` and `(q+2)^(TN)` is what makes the schedule reusable: a *mixed* two-`q` extraction
([Cop97]; `Examples/CoppersmithMixedPowerType.lean`) supplies the same statement with
`A = 7^{b₇}·6^{b₆}` and `R = 9^{9a}·8^{8b}` and inherits the whole schedule. -/
theorem cwRect_scheduleExtraction (q p m u v : ℕ) (hp : 0 < p) (hm : 0 < m) :
    RectangularScheduleExtraction K (q ^ m) (q ^ p) ((q + 2) ^ (p + 2 * m + 2 * u + v))
      (fun N ↦ (cwRectTypeWords (p * N) (m * N) (u * N) (v * N)).card)
      (fun N ↦ cwRectTypedFiberBound (p * N) (m * N) (u * N) (v * N)) := by
  classical
  intro N hN F _ _ _ hcard B hB
  have hapos : 0 < p * N := Nat.mul_pos hp hN
  have hmass : 0 < p * N + 2 * (m * N) + 2 * (u * N) + v * N := by omega
  obtain ⟨seed, hcount, hrestrict⟩ :=
    exists_cwPower_rectangularExtraction_of_fieldCard K q (p * N) (m * N) (u * N) (v * N) hmass
      B hB hcard
  refine ⟨↥((cwPartitionHashEncoding (R := F)).legwiseIsolatedPowerAddresses
      (cwRectDepth (p * N) (m * N) (u * N) (v * N))
      (cwRectTypeWords (p * N) (m * N) (u * N) (v * N)) B seed),
    inferInstance, ?_, ?_⟩
  · simpa [Fintype.card_coe] using hcount
  · have hdepth : cwRectDepth (p * N) (m * N) (u * N) (v * N) + 1 =
        p * N + 2 * (m * N) + 2 * (u * N) + v * N := cwRectDepth_add_one hmass
    have hborderPower :
        BorderRankLE ((q + 2) ^ (cwRectDepth (p * N) (m * N) (u * N) (v * N) + 1))
          (Tensor.power (cwPartitionedTensor K q).realize
            (cwRectDepth (p * N) (m * N) (u * N) (v * N) + 1)) :=
      (cwPartitionedTensor_borderRankLE K q).power _
    have hborder := hborderPower.of_restricts hrestrict
    rw [hdepth] at hborder
    have hAeq : (q ^ m) ^ N = q ^ (m * N) := by rw [← pow_mul]
    have hCeq : (q ^ p) ^ N = q ^ (p * N) := by rw [← pow_mul]
    have hReq : ((q + 2) ^ (p + 2 * m + 2 * u + v)) ^ N =
        (q + 2) ^ (p * N + 2 * (m * N) + 2 * (u * N) + v * N) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [hAeq, hCeq, hReq]
    exact hborder

/-- **One step of the Huang--Pan schedule, at an arbitrary competitor bound `F`.**  At depth `N`
the rectangular extraction produces a prime hashing modulus `M ≍ F`, a copy count, and -- after
compression at a near-optimal `κ`-rectangular algorithm of exponent `τ` -- the displayed
rectangular exponent inequality.

`F` only has to dominate the type-restricted competitor count at the scaled parameters; a smaller
`F` gives a smaller modulus and hence a better rate.  The copy count enters raised to `ω/τ`; the
factor `2^ω` is the compression rounding of `exists_compressionScale` and `D` is the constant of
the admissible exponent `τ`.

This is `AlgebraicComplexity.exists_rectSchedule_finite_step` at the full-CW extraction. -/
theorem exists_cwRect_finite_step_of_fiberBound (q p m u v : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) {N : ℕ} (hN : 0 < N)
    {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (rectangularMatrixRankSequence K (cwRectKappa p m) n : ℝ) ≤ D * (n : ℝ) ^ τ)
    (F : ℕ) (hF : cwRectTypedFiberBound (p * N) (m * N) (u * N) (v * N) ≤ F) :
    ∃ M copies : ℕ,
      M.Prime ∧ 12 * F < M ∧ M ≤ 24 * F ∧
      3 * (cwRectTypeWords (p * N) (m * N) (u * N) (v * N)).card * rothNumberNat (M / 2) ≤
        4 * (M * M) * copies ∧
      (((copies : ℝ) / D) ^ (1 / τ)) ^ (rectangularOmega K (cwRectKappa p m)) *
          (((q : ℝ) ^ (m * N)) ^ (rectangularOmega K (cwRectKappa p m))) ≤
        (2 : ℝ) ^ (rectangularOmega K (cwRectKappa p m)) *
          (((q + 2 : ℕ) : ℝ) ^ ((p + 2 * m + 2 * u + v) * N)) := by
  have hFpos : 0 < F := lt_of_lt_of_le (cwRectTypedFiberBound_pos _ _ _ _) hF
  have hA : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq
  have hR : 1 ≤ (q + 2) ^ (p + 2 * m + 2 * u + v) := Nat.one_le_pow _ _ (by omega)
  obtain ⟨M, copies, hprime, hlower, hupper, hcount, hstep⟩ :=
    exists_rectSchedule_finite_step K (rectAspectRatio_nonneg p m) hA hR
      (natPow_rpow_rectAspectRatio_le q p m hm) (cwRect_scheduleExtraction K q p m u v hp hm)
      hN hτ hD hbound F hFpos hF
  refine ⟨M, copies, hprime, hlower, hupper, hcount, ?_⟩
  have hAcast : (((q ^ m : ℕ)) : ℝ) ^ N = (q : ℝ) ^ (m * N) := by
    push_cast
    rw [← pow_mul]
  have hRcast : ((((q + 2) ^ (p + 2 * m + 2 * u + v) : ℕ)) : ℝ) ^ N =
      ((q + 2 : ℕ) : ℝ) ^ ((p + 2 * m + 2 * u + v) * N) := by
    push_cast
    rw [← pow_mul]
  rw [hAcast, hRcast] at hstep
  exact hstep

end FiniteStep

/-! ## The collected subexponential loss -/

/-- The subexponential loss of the rectangular schedule at depth `N` and competitor envelope `Φ`,
before the bootstrap exponent is applied: the type-counting loss, the Behrend/Bertrand loss, and
the constants `96` and `D`.  This is the shared `rectScheduleLossAt` at the six-fold multinomial
profile of this tower. -/
noncomputable def cwRectRateLossAt (p m u v : ℕ) (Φ D : ℝ) (N : ℕ) : ℝ :=
  rectScheduleLossAt (WordType.proportionalMultinomialLoss (cwRectType p m u v)) Φ D N

theorem cwRectRateLossAt_nonneg {p m u v : ℕ} {Φ D : ℝ} (hD : 0 ≤ D) (N : ℕ) :
    0 ≤ cwRectRateLossAt p m u v Φ D N :=
  rectScheduleLossAt_nonneg
    ((cwRectType_proportionalMultinomialLoss_subexponential p m u v).nonneg N) hD

theorem cwRectRateLossAt_subexponential (p m u v : ℕ) {Φ D : ℝ} (hΦ : 0 ≤ Φ) (hD : 0 ≤ D) :
    Growth.Subexponential (cwRectRateLossAt p m u v Φ D) :=
  rectScheduleLossAt_subexponential
    (cwRectType_proportionalMultinomialLoss_subexponential p m u v) hΦ hD

/-! ## The rate inequality and the master scalar inequality -/

section Rate

variable (K : Type u) [Field K]

/-- **The rectangular rate inequality at a fixed bootstrap exponent `τ` and competitor envelope
`Φ`.**

Every subexponential loss of the schedule is removed by
`Growth.le_of_pow_succ_le_subexponential_mul_pow_succ`; what survives is the Huang--Pan growth
constant `E₀ / Φ` raised to `ω/τ`, the price of having built the compression scale from an
admissible exponent `τ` rather than from `ω` itself.

This is `AlgebraicComplexity.rectSchedule_rate_inequality` at the full-CW extraction. -/
theorem cwRect_rate_inequality_of_fiberGrowth (q p m u v : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v)
    {Φ : ℝ} (hΦ : 1 ≤ Φ)
    (hfiber : ∀ N : ℕ,
      ((cwRectTypedFiberBound (p * N) (m * N) (u * N) (v * N) : ℕ) : ℝ) ≤ Φ ^ N)
    {τ : ℝ} (hτ : rectangularOmega K (cwRectKappa p m) < τ) :
    (cwRectEntropyBase p m u v / Φ) ^ (rectangularOmega K (cwRectKappa p m) / τ) *
        (q : ℝ) ^ ((m : ℝ) * rectangularOmega K (cwRectKappa p m)) ≤
      ((q + 2 : ℕ) : ℝ) ^ (p + 2 * m + 2 * u + v) := by
  have hA : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq
  have hR : 1 ≤ (q + 2) ^ (p + 2 * m + 2 * u + v) := Nat.one_le_pow _ _ (by omega)
  have hkey := rectSchedule_rate_inequality K (rectAspectRatio_nonneg p m) hA hR
    (natPow_rpow_rectAspectRatio_le q p m hm)
    (cwRect_scheduleExtraction K q p m u v hp hm)
    (fun N _ ↦ cwRectTypedFiberBound_pos (p * N) (m * N) (u * N) (v * N))
    (cwRectEntropyBase_pos hp hm hu hv)
    (cwRectType_proportionalMultinomialLoss_subexponential p m u v)
    (fun N hNpos ↦ cwRectType_entropyBase_pow_le_loss_mul_card hp hm hu hv hNpos) hΦ hfiber hτ
  rwa [natCast_pow_rpow, Nat.cast_pow] at hkey

/-- **The master scalar inequality of the rectangular full-CW pipeline, at an arbitrary competitor
envelope `Φ`.**

Letting the bootstrap exponent `τ` decrease to `ω(1,1,p/m)` removes the last artefact of
`cwRect_rate_inequality_of_fiberGrowth`.  This is Huang--Pan's Section 7 inequality in
denominator-free form. -/
theorem cwRect_master_inequality_of_fiberGrowth (q p m u v : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) (hu : 0 < u) (hv : 0 < v)
    {Φ : ℝ} (hΦ : 1 ≤ Φ)
    (hfiber : ∀ N : ℕ,
      ((cwRectTypedFiberBound (p * N) (m * N) (u * N) (v * N) : ℕ) : ℝ) ≤ Φ ^ N) :
    cwRectEntropyBase p m u v / Φ *
        (q : ℝ) ^ ((m : ℝ) * rectangularOmega K (cwRectKappa p m)) ≤
      ((q + 2 : ℕ) : ℝ) ^ (p + 2 * m + 2 * u + v) := by
  have hA : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq
  have hR : 1 ≤ (q + 2) ^ (p + 2 * m + 2 * u + v) := Nat.one_le_pow _ _ (by omega)
  have hkey := rectSchedule_master_inequality K (rectAspectRatio_nonneg p m) hA hR
    (natPow_rpow_rectAspectRatio_le q p m hm)
    (cwRect_scheduleExtraction K q p m u v hp hm)
    (fun N _ ↦ cwRectTypedFiberBound_pos (p * N) (m * N) (u * N) (v * N))
    (cwRectEntropyBase_pos hp hm hu hv)
    (cwRectType_proportionalMultinomialLoss_subexponential p m u v)
    (fun N hNpos ↦ cwRectType_entropyBase_pow_le_loss_mul_card hp hm hu hv hNpos) hΦ hfiber
  rwa [natCast_pow_rpow, Nat.cast_pow] at hkey

end Rate

end AlgebraicComplexity.Examples
