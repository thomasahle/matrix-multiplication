/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LaserVolume
import AlgebraicComplexity.MatrixMultiplication.TauValueSoundness

/-!
# Regularization: a laser volume sequence is a value certificate at every repetition

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module is the missing bridge between
the two upper-bound interfaces of the library:

* the *rate* interface `SubexponentialLaserVolumeSequence`
  (`MatrixMultiplication/LaserVolume.lean`), produced by type counting, hashing, compatibility
  cleanup, and hole repair — per-repetition degenerations of `T^{⊗(stride·r)}` onto `count r`
  copies of one rectangular tensor, with a certified subexponential loss in the copy count;
* the *value* interface `TauValueCertificate` / `tauValue`
  (`MatrixMultiplication/TauValueCore.lean`, `MatrixMultiplication/TauValueSoundness.lean`), the
  CW90 `V_τ` calculus with its three value laws.

Until now the two interfaces met only in the shared Schönhage soundness ingredient, and every laser
endpoint carried its own `SubexponentialLaserVolumeSequence` plumbing all the way to `omega`.  The
regularization theorem below turns a rate witness into a genuine family of value certificates, so an
endpoint can be stated in the value idiom — *`V_τ(source) ≥ v`, hence `ω < 3τ`* — with the sequence
appearing only as the input of a single named theorem.

## Mathematical content

Write `V_r = xSize r * ySize r * zSize r` for the rectangular volume of repetition `r`.  The
`r`-th member of a `SubexponentialLaserVolumeSequence K T stride copyBase volumeBase` *is*,
verbatim, a `TauValueCertificate K T` of power `stride * r` (`toTauValueCertificate`); the only
content is numerical.  Its weight at exponent `τ ≥ 0` is

```text
term τ = (count r · V_r^τ)^{1/(stride·r)} ≥
         ((copyBase^r / loss r) · volumeBase^{rτ})^{1/(stride·r)},
```

whose logarithm is `(log copyBase + τ · log volumeBase) / stride − log (loss r)/(stride·r)`.  The
first summand is the *stride-normalized* rate — one copy of `T` at a time, exactly the normalization
`HasLaserExtractionRate` uses — and it does not depend on `r`.  The second is killed by the
subexponential-loss absorption `exists_pos_log_loss_le_mul`, which is reused unchanged from
`LaserVolume.lean` rather than re-proved.  Hence the sequence certifies the value

```text
laserVolumeValue stride copyBase volumeBase τ = exp ((log copyBase + τ · log volumeBase)/stride)
                                              = (copyBase · volumeBase^τ)^{1/stride}
```

approximately from below, at *every* exponent `τ ≥ 0` at once.

## Principal results

* `SubexponentialLaserVolumeSequence.toTauValueCertificate` — the finite, semiring-level
  reinterpretation of one repetition as a CW90 value certificate.
* `SubexponentialLaserVolumeSequence.exists_tauValueCertificate_term_ge` — **the regularization
  theorem.**  For every `ε > 0` there is a value certificate of weight at least
  `laserVolumeValue … τ − ε`.  This is precisely the `happrox` hypothesis shape of
  `omega_lt_three_mul_of_approximate_certificates`, so laser clients feed it verbatim.
* `SubexponentialLaserVolumeSequence.le_tauValue_of_bddAbove` and `.le_tauValue` — the supremum
  form `laserVolumeValue … τ ≤ V_τ(T)`, with boundedness supplied by the caller in general and by
  `tauValueValues_bddAbove` in the classical regime `τ ≤ ω/3`.
* `SubexponentialLaserVolumeSequence.laserVolumeValue_le_asymptoticRank` — the regularized
  soundness statement at the critical exponent, the unsymmetrized counterpart of
  `HasCyclicLaserExtractionRate.exp_le_degenerationValue`.
* `SubexponentialLaserVolumeSequence.omega_lt_three_mul_of_asymptoticRank_le` and
  `.omega_lt_three_mul_of_borderRankLE` — the endpoint idiom in one step, and
  `.omega_lt_of_borderRankLE_bits` in the base-two retained/mean-volume coordinates that numerical
  certificates are written in.

## Why the hypotheses are what they are

`0 ≤ τ` is needed exactly once, to push the volume growth bound `volumeBase^r ≤ V_r` through the
`τ`-th power; the value calculus is only ever read at `τ ∈ [0, ω/3]`, so it costs nothing.  Nothing
in this module needs a field until the Schönhage direction is invoked: the regularization theorem
itself, and the `tauValue` lower bound with a supplied bound, hold over a commutative semiring.

## Relation to the rate interface

This module does not replace `SubexponentialLaserVolumeSequence.hasLaserExtractionRate`; it
factors through the same numerical data and agrees with it on the nose.  At `τ = ω/3`,

```text
log (laserVolumeValue stride copyBase volumeBase (ω/3))
  = (log copyBase + (ω/3)·log volumeBase)/stride
```

is literally the rate `hasLaserExtractionRate` produces, so a client may use either route and obtain
the same numbers; `Examples/CoppersmithWinogradVolumeEndpointValue.lean` checks that on the
committed Coppersmith--Winograd endpoint.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

/-! ## The value certified by a volume sequence -/

/-- **The value a laser volume sequence certifies at exponent `τ`**, in stride-normalized form:

```text
laserVolumeValue stride copyBase volumeBase τ = (copyBase · volumeBase^τ)^{1/stride}.
```

The definition is given through `Real.exp` so that it is total and positive without positivity
hypotheses on the two bases; `laserVolumeValue_eq_rpow` is the product form, valid exactly when
the bases are positive (which every `SubexponentialLaserVolumeSequence` guarantees). -/
noncomputable def laserVolumeValue (stride : ℕ) (copyBase volumeBase τ : ℝ) : ℝ :=
  Real.exp ((Real.log copyBase + τ * Real.log volumeBase) / stride)

/-- The certified value is positive. -/
theorem laserVolumeValue_pos (stride : ℕ) (copyBase volumeBase τ : ℝ) :
    0 < laserVolumeValue stride copyBase volumeBase τ :=
  Real.exp_pos _

/-- The logarithm of the certified value is the stride-normalized laser rate at `τ`.  At
`τ = ω/3` this is exactly the rate produced by
`SubexponentialLaserVolumeSequence.hasLaserExtractionRate`. -/
theorem log_laserVolumeValue (stride : ℕ) (copyBase volumeBase τ : ℝ) :
    Real.log (laserVolumeValue stride copyBase volumeBase τ) =
      (Real.log copyBase + τ * Real.log volumeBase) / stride :=
  Real.log_exp _

/-- The product form of the certified value. -/
theorem laserVolumeValue_eq_rpow {stride : ℕ} {copyBase volumeBase : ℝ}
    (hcopy : 0 < copyBase) (hvolume : 0 < volumeBase) (τ : ℝ) :
    laserVolumeValue stride copyBase volumeBase τ =
      (copyBase * volumeBase ^ τ) ^ ((stride : ℝ)⁻¹) := by
  have hpow : (0 : ℝ) < volumeBase ^ τ := Real.rpow_pos_of_pos hvolume τ
  have hbase : (0 : ℝ) < copyBase * volumeBase ^ τ := mul_pos hcopy hpow
  unfold laserVolumeValue
  rw [Real.rpow_def_of_pos hbase, Real.log_mul hcopy.ne' hpow.ne', Real.log_rpow hvolume,
    div_eq_mul_inv]

/-- **Base-two coordinates.**  A stride whose copy base is `2^(stride·retained)` and whose
rectangular-volume base is `2^(3·stride·volume)` certifies the value `2^(retained + 3τ·volume)`.

At `τ = ω/3` the exponent is `retained + ω·volume`, the quantity every numerical laser certificate
in this library reports. -/
theorem laserVolumeValue_bits {stride : ℕ} (hstride : 0 < stride) (retained volume τ : ℝ) :
    laserVolumeValue stride ((2 : ℝ) ^ ((stride : ℝ) * retained))
        ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)) τ =
      (2 : ℝ) ^ (retained + 3 * τ * volume) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hstrideR : (stride : ℝ) ≠ 0 := by
    exact_mod_cast hstride.ne'
  unfold laserVolumeValue
  rw [Real.log_rpow h2, Real.log_rpow h2, Real.rpow_def_of_pos h2]
  congr 1
  field_simp

/-! ## Regularization -/

section Semiring

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

namespace SubexponentialLaserVolumeSequence

/-- **One repetition of a laser volume sequence, read as a CW90 value certificate.**

No numerical content: the certificate's power is the source length `stride * r`, its summands are
the `count r` equal rectangular tensors the sequence extracts, and its semantic field is the
sequence's own `extract` obligation. -/
def toTauValueCertificate {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase)
    (r : ℕ) (hr : 0 < r) : TauValueCertificate K T where
  power := stride * r
  copies := h.count r
  xSize := fun _ ↦ h.xSize r
  ySize := fun _ ↦ h.ySize r
  zSize := fun _ ↦ h.zSize r
  power_pos := Nat.mul_pos h.stride_pos hr
  copies_pos := h.count_pos r hr
  xSize_pos := fun _ ↦ h.xSize_pos r hr
  ySize_pos := fun _ ↦ h.ySize_pos r hr
  zSize_pos := fun _ ↦ h.zSize_pos r hr
  degenerates := h.extract r hr

/-- The weight of the `r`-th certificate in closed form: the copy count times one rectangular
volume power, normalized by the source length. -/
theorem term_toTauValueCertificate {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase)
    (r : ℕ) (hr : 0 < r) (τ : ℝ) :
    (h.toTauValueCertificate K r hr).term τ =
      ((h.count r : ℝ) * (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) ^ τ) ^
        (((stride * r : ℕ) : ℝ)⁻¹) := by
  have hconst := matrixMultiplicationVolumePowerSum_const
    (h.count r) (h.xSize r) (h.ySize r) (h.zSize r) τ
  show matrixMultiplicationVolumePowerSum
      (fun _ : Fin (h.count r) ↦ h.xSize r) (fun _ : Fin (h.count r) ↦ h.ySize r)
      (fun _ : Fin (h.count r) ↦ h.zSize r) τ ^ (((stride * r : ℕ) : ℝ)⁻¹) =
    ((h.count r : ℝ) * (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) ^ τ) ^
      (((stride * r : ℕ) : ℝ)⁻¹)
  rw [hconst]

/-- **The finite half of regularization.**  At every repetition the logarithmic weight of the
associated value certificate is at least the stride-normalized rate minus the per-repetition
logarithmic loss.

Proof sketch: the copy-count and volume growth hypotheses are added after weighting the second by
`τ ≥ 0`, and the sum is divided by the positive source length `stride * r`. -/
theorem log_laserVolumeValue_sub_le_log_term {T : Tensor3 K V} {stride : ℕ}
    {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase)
    {τ : ℝ} (hτ : 0 ≤ τ) {r : ℕ} (hr : 0 < r) :
    (Real.log copyBase + τ * Real.log volumeBase) / stride -
        Real.log (h.loss r) / ((stride : ℝ) * r) ≤
      Real.log ((h.toTauValueCertificate K r hr).term τ) := by
  have hstride : (0 : ℝ) < stride := by exact_mod_cast h.stride_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsne : (stride : ℝ) ≠ 0 := hstride.ne'
  have hrne : (r : ℝ) ≠ 0 := hrR.ne'
  have hpos : (0 : ℝ) < (stride : ℝ) * r := mul_pos hstride hrR
  have hcount : (0 : ℝ) < ((h.count r : ℕ) : ℝ) := by exact_mod_cast h.count_pos r hr
  have hvol : (0 : ℝ) < (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (h.xSize_pos r hr) (h.ySize_pos r hr))
      (h.zSize_pos r hr)
  have hvolpow : (0 : ℝ) < (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) ^ τ :=
    Real.rpow_pos_of_pos hvol τ
  have hcopyLog : (r : ℝ) * Real.log copyBase ≤
      Real.log (h.loss r) + Real.log ((h.count r : ℕ) : ℝ) := by
    have hlog := Real.log_le_log (pow_pos h.copyBase_pos r) (h.copy_growth r hr)
    rwa [Real.log_pow, Real.log_mul (h.loss_pos r hr).ne' hcount.ne'] at hlog
  have hvolLog : (r : ℝ) * Real.log volumeBase ≤
      Real.log (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) := by
    have hlog := Real.log_le_log (pow_pos h.volumeBase_pos r) (h.volume_growth r hr)
    rwa [Real.log_pow] at hlog
  have hkey : (r : ℝ) * (Real.log copyBase + τ * Real.log volumeBase) - Real.log (h.loss r) ≤
      Real.log ((h.count r : ℕ) : ℝ) +
        τ * Real.log (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) := by
    have hweighted := mul_le_mul_of_nonneg_left hvolLog hτ
    nlinarith [hcopyLog, hweighted]
  have hterm : Real.log ((h.toTauValueCertificate K r hr).term τ) =
      ((Real.log ((h.count r : ℕ) : ℝ) +
        τ * Real.log (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)))) /
          ((stride : ℝ) * r) := by
    rw [term_toTauValueCertificate, Real.log_rpow (mul_pos hcount hvolpow),
      Real.log_mul hcount.ne' hvolpow.ne', Real.log_rpow hvol]
    push_cast
    ring
  have hrewrite : (Real.log copyBase + τ * Real.log volumeBase) / stride -
      Real.log (h.loss r) / ((stride : ℝ) * r) =
      ((r : ℝ) * (Real.log copyBase + τ * Real.log volumeBase) - Real.log (h.loss r)) /
        ((stride : ℝ) * r) := by
    field_simp [hsne, hrne]
  rw [hterm, hrewrite]
  exact div_le_div_of_nonneg_right hkey hpos.le

/-- **The regularization theorem.**  A rate witness is a value witness: for every `ε > 0` the
sequence supplies a finite CW90 value certificate of `T` whose weight at `τ` is within `ε` of the
certified value `laserVolumeValue stride copyBase volumeBase τ`.

This is exactly the `happrox` hypothesis of
`AlgebraicComplexity.omega_lt_three_mul_of_approximate_certificates`, which is why laser endpoints
need no supremum, no limit, and no attainment argument.

Proof sketch: request the loss budget `η = stride · ε / v` from `exists_pos_log_loss_le_mul`, where
`v` is the certified value; the finite half above then bounds the logarithmic weight below by
`log v − η/stride`, and `1 + x ≤ exp x` converts the multiplicative slack `exp (−η/stride)` into
the additive slack `ε`. -/
theorem exists_tauValueCertificate_term_ge {T : Tensor3 K V} {stride : ℕ}
    {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase)
    {τ : ℝ} (hτ : 0 ≤ τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ certificate : TauValueCertificate K T,
      laserVolumeValue stride copyBase volumeBase τ - ε ≤ certificate.term τ := by
  have hstride : (0 : ℝ) < stride := by exact_mod_cast h.stride_pos
  set v : ℝ := laserVolumeValue stride copyBase volumeBase τ
  have hvpos : 0 < v := laserVolumeValue_pos stride copyBase volumeBase τ
  set eta : ℝ := (stride : ℝ) * ε / v with heta
  have hetapos : 0 < eta := by
    rw [heta]
    exact div_pos (mul_pos hstride hε) hvpos
  obtain ⟨r, hr, hloss⟩ := exists_pos_log_loss_le_mul h.loss_subexponential h.loss_pos hetapos
  refine ⟨h.toTauValueCertificate K r hr, ?_⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hfinite := h.log_laserVolumeValue_sub_le_log_term K hτ hr
  have hlossBound : Real.log (h.loss r) / ((stride : ℝ) * r) ≤ eta / stride := by
    rw [div_le_div_iff₀ (mul_pos hstride hrR) hstride]
    nlinarith [mul_le_mul_of_nonneg_right hloss hstride.le]
  have hlogv : Real.log v = (Real.log copyBase + τ * Real.log volumeBase) / stride :=
    log_laserVolumeValue stride copyBase volumeBase τ
  have hlower : Real.log v - eta / stride ≤
      Real.log ((h.toTauValueCertificate K r hr).term τ) := by
    rw [hlogv]
    linarith
  have htermpos : 0 < (h.toTauValueCertificate K r hr).term τ :=
    TauValueCertificate.term_pos _ τ
  have hexp : Real.exp (Real.log v - eta / stride) ≤
      (h.toTauValueCertificate K r hr).term τ := by
    calc Real.exp (Real.log v - eta / stride) ≤
        Real.exp (Real.log ((h.toTauValueCertificate K r hr).term τ)) :=
          Real.exp_le_exp.mpr hlower
      _ = (h.toTauValueCertificate K r hr).term τ := Real.exp_log htermpos
  have hsplit : Real.exp (Real.log v - eta / stride) = v * Real.exp (-(eta / stride)) := by
    rw [show Real.log v - eta / stride = Real.log v + -(eta / stride) by ring, Real.exp_add,
      Real.exp_log hvpos]
  have hlinear : 1 - eta / stride ≤ Real.exp (-(eta / stride)) := by
    have := Real.add_one_le_exp (-(eta / stride))
    linarith
  have hslack : v * (1 - eta / stride) ≤ v * Real.exp (-(eta / stride)) :=
    mul_le_mul_of_nonneg_left hlinear hvpos.le
  have hvne : v ≠ 0 := hvpos.ne'
  have hsne : (stride : ℝ) ≠ 0 := hstride.ne'
  have hεeq : v * (eta / stride) = ε := by
    rw [heta]
    field_simp [hvne, hsne]
  have hexact : v * (1 - eta / stride) = v - ε := by
    rw [mul_sub, mul_one, hεeq]
  rw [← hexact]
  calc v * (1 - eta / stride) ≤ v * Real.exp (-(eta / stride)) := hslack
    _ = Real.exp (Real.log v - eta / stride) := hsplit.symm
    _ ≤ (h.toTauValueCertificate K r hr).term τ := hexp

/-- **The supremum form of regularization**, with boundedness supplied by the caller:
`laserVolumeValue … τ ≤ V_τ(T)`.

The library convention is to keep `BddAbove` explicit at this level, because `tauValue` is a bare
`sSup` and is meaningless without it; `le_tauValue` discharges it in the classical regime. -/
theorem le_tauValue_of_bddAbove {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase)
    {τ : ℝ} (hτ : 0 ≤ τ) (hbdd : BddAbove (tauValueValues K T τ)) :
    laserVolumeValue stride copyBase volumeBase τ ≤ tauValue K T τ := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨certificate, hcertificate⟩ := h.exists_tauValueCertificate_term_ge K hτ hε
  have hmem : certificate.term τ ≤ tauValue K T τ :=
    le_csSup hbdd (certificate.mem_tauValueValues τ)
  linarith

end SubexponentialLaserVolumeSequence

end Semiring

/-! ## Soundness consequences over a field -/

section Field

variable (F : Type u) [Field F]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

namespace SubexponentialLaserVolumeSequence

/-- **The regularized soundness statement at the critical exponent.**  The value certified by a
laser volume sequence never exceeds the asymptotic rank of its source:

```text
laserVolumeValue stride copyBase volumeBase (ω/3) ≤ R̃(T).
```

This is the unsymmetrized counterpart of `HasCyclicLaserExtractionRate.exp_le_degenerationValue`,
and the exact content of `HasLaserExtractionRate.le_log_borderRank` read multiplicatively: taking
logarithms recovers `rate ≤ log R̃(T)`.

Proof sketch: regularize with the slack `(v − R̃(T))/2` and apply certificate-level Schönhage
soundness to the resulting certificate. -/
theorem laserVolumeValue_le_asymptoticRank {T : Tensor3 F V} {stride : ℕ}
    {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence F T stride copyBase volumeBase) :
    laserVolumeValue stride copyBase volumeBase (omega F / 3) ≤ Tensor.asymptoticRank T := by
  by_contra hcontra
  have hlt : Tensor.asymptoticRank T <
      laserVolumeValue stride copyBase volumeBase (omega F / 3) := not_le.mp hcontra
  have hτ : (0 : ℝ) ≤ omega F / 3 := by
    have := omega_nonneg F
    linarith
  obtain ⟨certificate, hcertificate⟩ :=
    h.exists_tauValueCertificate_term_ge F hτ (half_pos (sub_pos.mpr hlt))
  have hsound := certificate.term_le_asymptoticRank (F := F)
  linarith

/-- The supremum form in the classical regime `0 ≤ τ ≤ ω/3`, where boundedness of the value set is
automatic (`tauValueValues_bddAbove`). -/
theorem le_tauValue {T : Tensor3 F V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence F T stride copyBase volumeBase)
    {τ : ℝ} (hτ : 0 ≤ τ) (hcritical : τ ≤ omega F / 3) :
    laserVolumeValue stride copyBase volumeBase τ ≤ tauValue F T τ :=
  h.le_tauValue_of_bddAbove F hτ (tauValueValues_bddAbove F hcritical)

/-- **The endpoint idiom, in one step.**  If the asymptotic rank of the source is at most `ρ` and
the sequence certifies strictly more than `ρ` at the exponent `τ ≥ 0`, then `ω < 3τ`.

This is the theorem laser endpoint clients should consume: it replaces the per-generation
composition of a rate theorem, a border-rank bound, and a hand-rolled solve-for-`omega` step. -/
theorem omega_lt_three_mul_of_asymptoticRank_le {T : Tensor3 F V} {stride : ℕ}
    {copyBase volumeBase ρ τ : ℝ}
    (h : SubexponentialLaserVolumeSequence F T stride copyBase volumeBase)
    (hτ : 0 ≤ τ) (hrank : Tensor.asymptoticRank T ≤ ρ)
    (hstrict : ρ < laserVolumeValue stride copyBase volumeBase τ) :
    omega F < 3 * τ :=
  omega_lt_three_mul_of_approximate_certificates F hrank hstrict
    (fun _ε hε ↦ h.exists_tauValueCertificate_term_ge F hτ hε)

/-- The same statement against a constructive border-rank certificate for the source, which is
what a paper client actually exhibits. -/
theorem omega_lt_three_mul_of_borderRankLE {T : Tensor3 F V} {stride : ℕ}
    {copyBase volumeBase τ : ℝ} {b : ℕ}
    (h : SubexponentialLaserVolumeSequence F T stride copyBase volumeBase)
    (hτ : 0 ≤ τ) (hborder : BorderRankLE b T)
    (hstrict : (b : ℝ) < laserVolumeValue stride copyBase volumeBase τ) :
    omega F < 3 * τ := by
  refine h.omega_lt_three_mul_of_asymptoticRank_le F hτ ?_ hstrict
  refine (Tensor.asymptoticRank_le_borderRank T).trans ?_
  exact_mod_cast Tensor.borderRank_le_iff.mpr hborder

/-- The base-two form: a sequence with retained exponent `retained` and mean rectangular side
exponent `volume` beats a border-rank certificate `b` at the target exponent `target` as soon as
`b < 2^(retained + target·volume)`.

The exponent bookkeeping is the one place a factor can slip, so it is discharged once here:
`τ = target/3` in the value calculus, `3τ·volume = target·volume` in the bit budget, and the
conclusion `ω < 3τ` is `ω < target`. -/
theorem omega_lt_of_borderRankLE_bits {T : Tensor3 F V} {stride : ℕ}
    {retained volume target : ℝ} {b : ℕ}
    (h : SubexponentialLaserVolumeSequence F T stride ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (htarget : 0 ≤ target) (hborder : BorderRankLE b T)
    (hstrict : (b : ℝ) < (2 : ℝ) ^ (retained + target * volume)) :
    omega F < target := by
  have hτ : (0 : ℝ) ≤ target / 3 := by linarith
  have hvalue : laserVolumeValue stride ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)) (target / 3) =
      (2 : ℝ) ^ (retained + target * volume) := by
    rw [laserVolumeValue_bits h.stride_pos,
      show retained + 3 * (target / 3) * volume = retained + target * volume by ring]
  have hmain := h.omega_lt_three_mul_of_borderRankLE F (τ := target / 3) hτ hborder
    (by rw [hvalue]; exact hstrict)
  linarith

end SubexponentialLaserVolumeSequence

end Field

end AlgebraicComplexity
