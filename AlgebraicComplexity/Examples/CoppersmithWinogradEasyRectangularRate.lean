/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.RpowInequalities
import AlgebraicComplexity.Examples.CoppersmithWinogradEasyRectangularHashing
import AlgebraicComplexity.MatrixMultiplication.RectangularSchedule

/-!
# The rectangular easy-CW rate inequality

This module instantiates the Huang--Pan schedule of
`MatrixMultiplication/RectangularSchedule.lean` -- `(a, b) = (p·N, m·N)`, `N → ∞` -- on the
rectangular extraction of `Examples/CoppersmithWinogradEasyRectangularHashing.lean`, ending at
the single scalar inequality

`(E₀ / Φ) · q ^ (m · ω(1,1,p/m)) ≤ (q+2) ^ (p + 2m)`,

where `E₀ = easyRectEntropyBase p m = (p+2m)^(p+2m) / (p^p · m^(2m))` is the Huang--Pan trinomial
growth rate and `Φ` is *any* geometric envelope of the hashing competitor count along the
schedule, i.e. any real with

`#competitors(p·N, m·N) ≤ Φ ^ N   for all N`

(`easyRect_master_inequality_of_fiberGrowth`).  The competitor count is Huang--Pan's `M`, the
type-restricted leg fiber `easyRectTypedFiberBound` of the hashing module.

## What is here and what is in the schedule module

Everything paper-independent -- Bertrand's modulus, Behrend's progression-free set, the
compression bootstrap, the three subexponential losses and their cancellation -- lives in
`MatrixMultiplication/RectangularSchedule.lean` and is shared with the full-CW rectangular tower
of `Examples/CoppersmithWinogradRectangularRate.lean`.  This module supplies only the four
instantiating data:

* the extraction, as `easyRect_scheduleExtraction`;
* the entropy base `easyRectEntropyBase` with its loss
  `WordType.proportionalMultinomialLoss (easyRectType p m)`;
* the word length `p + 2m`, which enters only through the border-rank bound;
* the geometric data `A = q^m`, `C = q^p`, `R = (q+2)^(p+2m)`.

## The two envelopes

* the whole-leg-fiber envelope `Φ = 2 ^ max (2m, p+m)` needs nothing beyond
  `easyRectTypedFiberBound_le`, and gives the specialization `easyRect_master_inequality`, from
  which `Examples/CoppersmithWinogradEasyRectangularBound.lean` reads Huang--Pan (6.2) and the
  weak form of (6.1);
* the binomial envelope `Φ = (p+m)^(p+m) / (p^p · m^m)` is sharp for `m ≤ p` and gives the sharp
  (6.1) in `Examples/CoppersmithWinogradEasyRectangularSharpBound.lean`.

Keeping `Φ` a parameter is what lets one schedule serve both branches: the entropy comparison
between the two envelopes is never needed, because each branch instantiates its own.

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299, Sections 6.1--6.2.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Growth

universe u

/-! ## The Huang--Pan schedule constants -/

/-- Huang--Pan's aspect ratio `r = p/m`, as a real number.  A tower-local spelling of the shared
`AlgebraicComplexity.rectAspectRatio`. -/
noncomputable abbrev easyRectKappa (p m : ℕ) : ℝ := rectAspectRatio p m

/-- The exponent of the hashing-field size along the schedule: `Λ = max (2m, p+m)`. -/
def easyRectFiberExponent (p m : ℕ) : ℕ := max (2 * m) (p + m)

/-- The trinomial growth base of the rectangular type: `(p+2m)^(p+2m) / (p^p · m^(2m))`. -/
noncomputable def easyRectEntropyBase (p m : ℕ) : ℝ :=
  ((p + 2 * m : ℕ) : ℝ) ^ (p + 2 * m) / ((p : ℝ) ^ p * (m : ℝ) ^ (2 * m))

/-- The Huang--Pan growth constant after the whole-leg-fiber hashing loss: the trinomial base
divided by `2 ^ max (2m, p+m)`. -/
noncomputable def easyRectGrowth (p m : ℕ) : ℝ :=
  easyRectEntropyBase p m / ((2 ^ easyRectFiberExponent p m : ℕ) : ℝ)

theorem easyRectEntropyBase_pos {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    0 < easyRectEntropyBase p m := by
  unfold easyRectEntropyBase
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsum : (0 : ℝ) < ((p + 2 * m : ℕ) : ℝ) := by
    have : 0 < p + 2 * m := by omega
    exact_mod_cast this
  positivity

theorem easyRectGrowth_pos {p m : ℕ} (hp : 0 < p) (hm : 0 < m) :
    0 < easyRectGrowth p m := by
  unfold easyRectGrowth
  have := easyRectEntropyBase_pos hp hm
  have hden : (0 : ℝ) < ((2 ^ easyRectFiberExponent p m : ℕ) : ℝ) := by
    have : 0 < 2 ^ easyRectFiberExponent p m := pow_pos (by norm_num) _
    exact_mod_cast this
  positivity

/-- Along the schedule the whole-fiber bound is the geometric sequence `(2 ^ Λ) ^ N`. -/
theorem easyRectFiberBound_scaled (p m N : ℕ) :
    easyRectFiberBound (p * N) (m * N) = (2 ^ easyRectFiberExponent p m) ^ N := by
  unfold easyRectFiberBound easyRectFiberExponent
  rw [← pow_mul]
  congr 1
  rcases le_total (2 * m) (p + m) with h | h
  · have h' : 2 * (m * N) ≤ p * N + m * N := by
      calc 2 * (m * N) = 2 * m * N := by ring
        _ ≤ (p + m) * N := Nat.mul_le_mul_right N h
        _ = p * N + m * N := by ring
    rw [max_eq_right h, max_eq_right h']
    ring
  · have h' : p * N + m * N ≤ 2 * (m * N) := by
      calc p * N + m * N = (p + m) * N := by ring
        _ ≤ 2 * m * N := Nat.mul_le_mul_right N h
        _ = 2 * (m * N) := by ring
    rw [max_eq_left h, max_eq_left h']
    ring

/-- The whole-leg-fiber envelope of the type-restricted competitor count along the schedule. -/
theorem easyRectTypedFiberBound_scaled_le (p m N : ℕ) :
    ((easyRectTypedFiberBound (p * N) (m * N) : ℕ) : ℝ) ≤
      (((2 ^ easyRectFiberExponent p m : ℕ) : ℝ)) ^ N := by
  have hnat : easyRectTypedFiberBound (p * N) (m * N) ≤ (2 ^ easyRectFiberExponent p m) ^ N :=
    (easyRectTypedFiberBound_le (p * N) (m * N)).trans
      (le_of_eq (easyRectFiberBound_scaled p m N))
  calc ((easyRectTypedFiberBound (p * N) (m * N) : ℕ) : ℝ)
      ≤ (((2 ^ easyRectFiberExponent p m) ^ N : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (((2 ^ easyRectFiberExponent p m : ℕ) : ℝ)) ^ N := by push_cast; ring

/-- The rectangular constituent really has aspect ratio `κ = p/m`: the outer dimension `q^(pN)`
is exactly the `κ`-th power of the inner dimension `q^(mN)`.  A tower-local spelling of
`AlgebraicComplexity.rectAspectRatio_pow_rpow`. -/
theorem easyRect_rpow_kappa (q p m N : ℕ) (hm : 0 < m) :
    ((q : ℝ) ^ (m * N)) ^ easyRectKappa p m = (q : ℝ) ^ (p * N) :=
  rectAspectRatio_pow_rpow q p m N hm

/-! ## The extraction, in the shape the schedule consumes -/

section FiniteStep

variable (K : Type u) [Field K]

/-- **The easy-CW rectangular extraction as a schedule input.**

At depth `N` the selected type has `(easyRectTypeWords (p·N) (m·N)).card` words and competitor
count `easyRectTypedFiberBound (p·N) (m·N)`, and the extracted constituents are
`⟨(q^m)^N, (q^m)^N, (q^p)^N⟩` inside a tensor of border rank `((q+2)^(p+2m))^N`.  Presenting the
extraction in the abstract `(A, C, R)` form of `RectangularScheduleExtraction` is what lets the
shared schedule run on it. -/
theorem easyRect_scheduleExtraction (q p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    RectangularScheduleExtraction K (q ^ m) (q ^ p) ((q + 2) ^ (p + 2 * m))
      (fun N ↦ (easyRectTypeWords (p * N) (m * N)).card)
      (fun N ↦ easyRectTypedFiberBound (p * N) (m * N)) := by
  classical
  intro N hN F _ _ _ hcard B hB
  have hapos : 0 < p * N := Nat.mul_pos hp hN
  have hmass : 0 < p * N + 2 * (m * N) := by omega
  obtain ⟨seed, hcount, hrestrict⟩ :=
    exists_easyPower_rectangularExtraction_of_fieldCard_typed K q (p * N) (m * N) hmass B hB
      hcard
  refine ⟨↥((easyPartitionHashEncoding (R := F)).legwiseIsolatedPowerAddresses
      (easyRectTypeDepth (p * N) (m * N)) (easyRectTypeWords (p * N) (m * N)) B seed),
    inferInstance, ?_, ?_⟩
  · simpa [Fintype.card_coe] using hcount
  · have hdepth : easyRectTypeDepth (p * N) (m * N) + 1 = p * N + 2 * (m * N) :=
      easyRectTypeDepth_add_one hmass
    have hborderPower :
        BorderRankLE ((q + 2) ^ (easyRectTypeDepth (p * N) (m * N) + 1))
          (Tensor.power (easyPartitionedTensor K q).realize
            (easyRectTypeDepth (p * N) (m * N) + 1)) :=
      (easyPartitionedTensor_borderRankLE K q).power _
    have hborder := hborderPower.of_restricts hrestrict
    rw [hdepth] at hborder
    have hAeq : (q ^ m) ^ N = q ^ (m * N) := by rw [← pow_mul]
    have hCeq : (q ^ p) ^ N = q ^ (p * N) := by rw [← pow_mul]
    have hReq : ((q + 2) ^ (p + 2 * m)) ^ N = (q + 2) ^ (p * N + 2 * (m * N)) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [hAeq, hCeq, hReq]
    exact hborder

/-- **One step of the Huang--Pan schedule, at an arbitrary competitor bound `F`.**  At depth `N`
the rectangular extraction produces a prime hashing modulus `M ≍ F`, a copy count, and — after
compression at a near-optimal `κ`-rectangular algorithm of exponent `τ` — the displayed
rectangular exponent inequality.

`F` only has to dominate the type-restricted competitor count `easyRectTypedFiberBound` at the
scaled parameters; a smaller `F` gives a smaller modulus and hence a better rate.

The copy count enters raised to `ω/τ`; the factor `2 ^ ω` is the compression rounding of
`exists_compressionScale` and `D` is the constant of the admissible exponent `τ`.

This is `AlgebraicComplexity.exists_rectSchedule_finite_step` at the easy-CW extraction. -/
theorem exists_easyRect_finite_step_of_fiberBound (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) {N : ℕ} (hN : 0 < N)
    {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (rectangularMatrixRankSequence K (easyRectKappa p m) n : ℝ) ≤ D * (n : ℝ) ^ τ)
    (F : ℕ) (hF : easyRectTypedFiberBound (p * N) (m * N) ≤ F) :
    ∃ M copies : ℕ,
      M.Prime ∧ 12 * F < M ∧ M ≤ 24 * F ∧
      3 * (easyRectTypeWords (p * N) (m * N)).card * rothNumberNat (M / 2) ≤
        4 * (M * M) * copies ∧
      (((copies : ℝ) / D) ^ (1 / τ)) ^ (rectangularOmega K (easyRectKappa p m)) *
          (((q : ℝ) ^ (m * N)) ^ (rectangularOmega K (easyRectKappa p m))) ≤
        (2 : ℝ) ^ (rectangularOmega K (easyRectKappa p m)) *
          (((q + 2 : ℕ) : ℝ) ^ ((p + 2 * m) * N)) := by
  have hFpos : 0 < F := lt_of_lt_of_le (easyRectTypedFiberBound_pos _ _) hF
  have hA : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq
  have hR : 1 ≤ (q + 2) ^ (p + 2 * m) := Nat.one_le_pow _ _ (by omega)
  obtain ⟨M, copies, hprime, hlower, hupper, hcount, hstep⟩ :=
    exists_rectSchedule_finite_step K (rectAspectRatio_nonneg p m) hA hR
      (natPow_rpow_rectAspectRatio_le q p m hm) (easyRect_scheduleExtraction K q p m hp hm) hN hτ hD
      hbound F hFpos hF
  refine ⟨M, copies, hprime, hlower, hupper, hcount, ?_⟩
  have hAcast : (((q ^ m : ℕ)) : ℝ) ^ N = (q : ℝ) ^ (m * N) := by
    push_cast
    rw [← pow_mul]
  have hRcast : ((((q + 2) ^ (p + 2 * m) : ℕ)) : ℝ) ^ N =
      ((q + 2 : ℕ) : ℝ) ^ ((p + 2 * m) * N) := by
    push_cast
    rw [← pow_mul]
  rw [hAcast, hRcast] at hstep
  exact hstep

/-- **One step of the Huang--Pan schedule at the whole-fiber competitor bound.**  This is
`exists_easyRect_finite_step_of_fiberBound` with `F = (2 ^ Λ) ^ N`. -/
theorem exists_easyRect_finite_step (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) {N : ℕ} (hN : 0 < N)
    {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (rectangularMatrixRankSequence K (easyRectKappa p m) n : ℝ) ≤ D * (n : ℝ) ^ τ) :
    ∃ M copies : ℕ,
      M.Prime ∧ 12 * (2 ^ easyRectFiberExponent p m) ^ N < M ∧
      M ≤ 24 * (2 ^ easyRectFiberExponent p m) ^ N ∧
      3 * (easyRectTypeWords (p * N) (m * N)).card * rothNumberNat (M / 2) ≤
        4 * (M * M) * copies ∧
      (((copies : ℝ) / D) ^ (1 / τ)) ^ (rectangularOmega K (easyRectKappa p m)) *
          (((q : ℝ) ^ (m * N)) ^ (rectangularOmega K (easyRectKappa p m))) ≤
        (2 : ℝ) ^ (rectangularOmega K (easyRectKappa p m)) *
          (((q + 2 : ℕ) : ℝ) ^ ((p + 2 * m) * N)) :=
  exists_easyRect_finite_step_of_fiberBound K q p m hq hp hm hN hτ hD hbound
    ((2 ^ easyRectFiberExponent p m) ^ N)
    ((easyRectTypedFiberBound_le (p * N) (m * N)).trans
      (le_of_eq (easyRectFiberBound_scaled p m N)))

end FiniteStep

/-! ## The collected subexponential loss and the rate inequality -/

/-- The subexponential loss of the rectangular schedule at depth `N` and competitor envelope `Φ`,
before the bootstrap exponent is applied: the type-counting loss, the Behrend/Bertrand loss, and
the constants `96` and `D`.  This is the shared `rectScheduleLossAt` at the trinomial profile of
this tower. -/
noncomputable def easyRectRateLossAt (p m : ℕ) (Φ D : ℝ) (N : ℕ) : ℝ :=
  rectScheduleLossAt (WordType.proportionalMultinomialLoss (easyRectType p m)) Φ D N

theorem easyRectRateLossAt_nonneg {p m : ℕ} {Φ D : ℝ} (hD : 0 ≤ D) (N : ℕ) :
    0 ≤ easyRectRateLossAt p m Φ D N :=
  rectScheduleLossAt_nonneg
    ((easyRectType_proportionalMultinomialLoss_subexponential p m).nonneg N) hD

theorem easyRectRateLossAt_subexponential (p m : ℕ) {Φ D : ℝ} (hΦ : 0 ≤ Φ) (hD : 0 ≤ D) :
    Growth.Subexponential (easyRectRateLossAt p m Φ D) :=
  rectScheduleLossAt_subexponential
    (easyRectType_proportionalMultinomialLoss_subexponential p m) hΦ hD

/-! ## The rate inequality and the master scalar inequality -/

section Rate

variable (K : Type u) [Field K]

/-- **The rectangular rate inequality at a fixed bootstrap exponent `τ` and competitor envelope
`Φ`.**

Every subexponential loss of the schedule is removed by
`Growth.le_of_pow_succ_le_subexponential_mul_pow_succ`; what survives is the Huang--Pan growth
constant `E₀ / Φ` raised to `ω/τ`, the price of having built the compression scale from an
admissible exponent `τ` rather than from `ω` itself.

This is `AlgebraicComplexity.rectSchedule_rate_inequality` at the easy-CW extraction. -/
theorem easyRect_rate_inequality_of_fiberGrowth (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) {Φ : ℝ} (hΦ : 1 ≤ Φ)
    (hfiber : ∀ N : ℕ, ((easyRectTypedFiberBound (p * N) (m * N) : ℕ) : ℝ) ≤ Φ ^ N)
    {τ : ℝ} (hτ : rectangularOmega K (easyRectKappa p m) < τ) :
    (easyRectEntropyBase p m / Φ) ^ (rectangularOmega K (easyRectKappa p m) / τ) *
        (q : ℝ) ^ ((m : ℝ) * rectangularOmega K (easyRectKappa p m)) ≤
      ((q + 2 : ℕ) : ℝ) ^ (p + 2 * m) := by
  have hA : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq
  have hR : 1 ≤ (q + 2) ^ (p + 2 * m) := Nat.one_le_pow _ _ (by omega)
  have hkey := rectSchedule_rate_inequality K (rectAspectRatio_nonneg p m) hA hR
    (natPow_rpow_rectAspectRatio_le q p m hm)
    (easyRect_scheduleExtraction K q p m hp hm)
    (fun N _ ↦ easyRectTypedFiberBound_pos (p * N) (m * N)) (easyRectEntropyBase_pos hp hm)
    (easyRectType_proportionalMultinomialLoss_subexponential p m)
    (fun N hNpos ↦ easyRectType_entropyBase_pow_le_loss_mul_card hp hm hNpos) hΦ hfiber hτ
  rwa [natCast_pow_rpow, Nat.cast_pow] at hkey

/-- **The rectangular rate inequality at the whole-fiber competitor bound.** -/
theorem easyRect_rate_inequality (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m)
    {τ : ℝ} (hτ : rectangularOmega K (easyRectKappa p m) < τ) :
    easyRectGrowth p m ^ (rectangularOmega K (easyRectKappa p m) / τ) *
        (q : ℝ) ^ ((m : ℝ) * rectangularOmega K (easyRectKappa p m)) ≤
      ((q + 2 : ℕ) : ℝ) ^ (p + 2 * m) := by
  have hone : (1 : ℝ) ≤ ((2 ^ easyRectFiberExponent p m : ℕ) : ℝ) := by
    have : 1 ≤ 2 ^ easyRectFiberExponent p m := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast this
  exact easyRect_rate_inequality_of_fiberGrowth K q p m hq hp hm hone
    (easyRectTypedFiberBound_scaled_le p m) hτ

/-- **The master scalar inequality of the rectangular easy-CW pipeline, at an arbitrary
competitor envelope `Φ`.**

Letting the bootstrap exponent `τ` decrease to `ω(1,1,p/m)` removes the last artefact of
`easyRect_rate_inequality_of_fiberGrowth`.  This is Huang--Pan's Section 6 inequality in
denominator-free form. -/
theorem easyRect_master_inequality_of_fiberGrowth (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) {Φ : ℝ} (hΦ : 1 ≤ Φ)
    (hfiber : ∀ N : ℕ, ((easyRectTypedFiberBound (p * N) (m * N) : ℕ) : ℝ) ≤ Φ ^ N) :
    easyRectEntropyBase p m / Φ *
        (q : ℝ) ^ ((m : ℝ) * rectangularOmega K (easyRectKappa p m)) ≤
      ((q + 2 : ℕ) : ℝ) ^ (p + 2 * m) := by
  have hA : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq
  have hR : 1 ≤ (q + 2) ^ (p + 2 * m) := Nat.one_le_pow _ _ (by omega)
  have hkey := rectSchedule_master_inequality K (rectAspectRatio_nonneg p m) hA hR
    (natPow_rpow_rectAspectRatio_le q p m hm)
    (easyRect_scheduleExtraction K q p m hp hm)
    (fun N _ ↦ easyRectTypedFiberBound_pos (p * N) (m * N)) (easyRectEntropyBase_pos hp hm)
    (easyRectType_proportionalMultinomialLoss_subexponential p m)
    (fun N hNpos ↦ easyRectType_entropyBase_pow_le_loss_mul_card hp hm hNpos) hΦ hfiber
  rwa [natCast_pow_rpow, Nat.cast_pow] at hkey

/-- **The master scalar inequality at the whole-fiber competitor bound.**

`Examples/CoppersmithWinogradEasyRectangularBound.lean` reads the two branches `r ≤ 1` and
`r ≥ 1` off it; the sharp `r ≥ 1` branch instead uses the binomial envelope in
`Examples/CoppersmithWinogradEasyRectangularSharpBound.lean`. -/
theorem easyRect_master_inequality (q p m : ℕ)
    (hq : 1 < q) (hp : 0 < p) (hm : 0 < m) :
    easyRectGrowth p m *
        (q : ℝ) ^ ((m : ℝ) * rectangularOmega K (easyRectKappa p m)) ≤
      ((q + 2 : ℕ) : ℝ) ^ (p + 2 * m) := by
  have hone : (1 : ℝ) ≤ ((2 ^ easyRectFiberExponent p m : ℕ) : ℝ) := by
    have : 1 ≤ 2 ^ easyRectFiberExponent p m := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast this
  exact easyRect_master_inequality_of_fiberGrowth K q p m hq hp hm hone
    (easyRectTypedFiberBound_scaled_le p m)

end Rate

end AlgebraicComplexity.Examples
