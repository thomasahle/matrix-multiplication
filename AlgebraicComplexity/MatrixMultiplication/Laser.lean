/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LaserRate
import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum

/-!
# Reusable laser-extraction interface

Laser arguments first zero a tensor power into many independent, isomorphic
matrix-multiplication tensors.  This file records that semantic certificate separately from the
combinatorics used to construct it and proves the finite inequality obtained from Schönhage's
asymptotic sum inequality.

* `HasLaserExtractionRate` is the semantic output of a hashing/typical-sequence argument: an
  arbitrarily small loss per source power, and a finite direct sum whose asymptotic-sum value
  realizes the claimed logarithmic rate.
* `HasLaserExtractionRate.of_uniformVolumeGrowth` is the shared analytic tail of *every* uniform
  laser-rate theorem in the library.  It takes the copy-count and rectangular-volume growth
  targets as logarithms, so the four-base interface below, the volume-native interface of
  `MatrixMultiplication/LaserVolume.lean`, and their subexponential-loss variants all reduce to it
  instead of repeating the `asymptoticSum_const`/`Real.log_mul`/`Real.log_rpow` computation.
* `UniformLaserBaseExtraction` is the four-base finite interface (a copy base and one base per
  rectangular side); `HasLaserExtractionRate.le_log_borderRank` is the soundness direction,
  bounding any achieved rate by `log` of the source border rank.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Semiring

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **The shared tail of every uniform laser-rate theorem.**  Suppose that for each requested
per-repetition copy-count loss `η > 0` there is a repetition `r > 0` and a uniform extraction of
`count` copies of `⟨m,n,p⟩` from `T^(stride*r)` whose logarithms satisfy

```text
r * (copyLog - η) ≤ log count        and        r * volumeLog ≤ log (m*n*p).
```

Then `T` achieves the logarithmic laser rate `(copyLog + (ω/3) * volumeLog) / stride`.

The two growth targets are supplied as *logarithms* rather than as bases, so that a client
certifying three separate side bases (`volumeLog = log xBase + log yBase + log zBase`), one
rectangular-volume base (`volumeLog = log volumeBase`), or any other additive combination can use
the same lemma; only the finite hypothesis differs.

Proof sketch: the asymptotic sum of `count` equal summands is `count * (m*n*p)^(ω/3)`
(`asymptoticSum_const`), so its logarithm is `log count + (ω/3) * log (m*n*p)`
(`Real.log_mul`, `Real.log_rpow`).  Asking the extractor for the loss `η = stride * ε` makes the
target `(stride*r) * (rate - ε)` equal to `r * (copyLog - η) + (ω/3) * (r * volumeLog)` on the
nose, and the two supplied bounds add — the second after weighting by `ω/3 ≥ 0`. -/
theorem HasLaserExtractionRate.of_uniformVolumeGrowth
    {T : Tensor3 K V} {stride : ℕ} {copyLog volumeLog : ℝ}
    (hstride : 0 < stride)
    (hextract : ∀ η : ℝ, 0 < η →
      ∃ (r count m n p : ℕ),
        0 < r ∧ 0 < count ∧ 0 < m ∧ 0 < n ∧ 0 < p ∧
          PolynomialDegenerates (Tensor.power T (stride * r))
            (matrixMultiplicationDirectSum (ι := Fin count) K
              (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p)) ∧
          (r : ℝ) * (copyLog - η) ≤ Real.log count ∧
          (r : ℝ) * volumeLog ≤ Real.log ((m * n * p : ℕ) : ℝ)) :
    HasLaserExtractionRate K T ((copyLog + (omega K / 3) * volumeLog) / stride) := by
  intro ε hε
  have hstrideReal : (0 : ℝ) < stride := by exact_mod_cast hstride
  have hstrideNe : (stride : ℝ) ≠ 0 := hstrideReal.ne'
  have hη : 0 < (stride : ℝ) * ε := by positivity
  obtain ⟨r, count, m, n, p, hr, hcount, hm, hn, hp, hdeg, hcopyLog, hvolumeLog⟩ :=
    hextract ((stride : ℝ) * ε) hη
  refine ⟨stride * r, count, (fun _ ↦ m), (fun _ ↦ n), (fun _ ↦ p),
    Nat.mul_pos hstride hr, (fun _ ↦ hm), (fun _ ↦ hn), (fun _ ↦ hp), hdeg, ?_, ?_⟩
  · rw [asymptoticSum_const]
    simp only [Fintype.card_fin]
    exact mul_pos (by exact_mod_cast hcount)
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.mul_pos (Nat.mul_pos hm hn) hp) _)
  · rw [asymptoticSum_const]
    simp only [Fintype.card_fin]
    have hcountReal : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
    have hvolumeReal : (0 : ℝ) < ((m * n * p : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.mul_pos hm hn) hp
    have homegaThird : 0 ≤ omega K / 3 :=
      div_nonneg (omega_nonneg K) (by norm_num)
    have hweighted := mul_le_mul_of_nonneg_left hvolumeLog homegaThird
    have hrpowPos : 0 < (((m * n * p : ℕ) : ℝ) ^ (omega K / 3)) :=
      Real.rpow_pos_of_pos hvolumeReal _
    rw [Real.log_mul hcountReal hrpowPos.ne', Real.log_rpow hvolumeReal]
    calc
      ((stride * r : ℕ) : ℝ) *
          ((copyLog + (omega K / 3) * volumeLog) / stride - ε) =
          (r : ℝ) * (copyLog - (stride : ℝ) * ε) +
            (omega K / 3) * ((r : ℝ) * volumeLog) := by
        push_cast
        field_simp [hstrideNe]
        ring
      _ ≤ Real.log count + (omega K / 3) * Real.log ((m * n * p : ℕ) : ℝ) :=
        add_le_add hcopyLog hweighted

/-- Finite uniform extractions realizing four exponential bases along a fixed power stride.

At repetition count `r`, the source is `T^(stride*r)`.  The output consists of `count`
independent copies of one rectangular tensor.  The three side logarithms have their exact target
growth, while the copy-count logarithm may lose an arbitrary positive amount `η` per
repetition.  This is the natural semantic endpoint of method-of-types counting, hashing, and
subexponential hole repair before applying Schönhage's asymptotic sum inequality.

The bases are real because entropy estimates naturally produce real exponential bases even when
the resulting finite counts and matrix dimensions are natural numbers. -/
structure UniformLaserBaseExtraction (T : Tensor3 K V)
    (stride : ℕ) (copyBase xBase yBase zBase : ℝ) : Prop where
  stride_pos : 0 < stride
  copyBase_pos : 0 < copyBase
  xBase_pos : 0 < xBase
  yBase_pos : 0 < yBase
  zBase_pos : 0 < zBase
  extract : ∀ η : ℝ, 0 < η →
    ∃ (r count m n p : ℕ),
      0 < r ∧ 0 < count ∧ 0 < m ∧ 0 < n ∧ 0 < p ∧
        PolynomialDegenerates (Tensor.power T (stride * r))
          (matrixMultiplicationDirectSum (ι := Fin count) K
            (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p)) ∧
        (r : ℝ) * (Real.log copyBase - η) ≤ Real.log count ∧
        (r : ℝ) * Real.log xBase ≤ Real.log m ∧
        (r : ℝ) * Real.log yBase ≤ Real.log n ∧
        (r : ℝ) * Real.log zBase ≤ Real.log p

namespace UniformLaserBaseExtraction

/-- Uniform finite base growth gives the corresponding logarithmic laser extraction rate.

Proof sketch: this is `HasLaserExtractionRate.of_uniformVolumeGrowth` at
`volumeLog = log xBase + log yBase + log zBase`.  The only work left here is to turn the three
side bounds `r * log xBase ≤ log m`, `r * log yBase ≤ log n`, `r * log zBase ≤ log p` into the
single rectangular-volume bound `r * (log xBase + log yBase + log zBase) ≤ log (m*n*p)`, which is
`Real.log_mul` twice on the positive natural sides. -/
theorem hasLaserExtractionRate
    {T : Tensor3 K V} {stride : ℕ} {copyBase xBase yBase zBase : ℝ}
    (h : UniformLaserBaseExtraction K T stride copyBase xBase yBase zBase) :
    HasLaserExtractionRate K T
      ((Real.log copyBase + (omega K / 3) *
        (Real.log xBase + Real.log yBase + Real.log zBase)) / stride) := by
  refine HasLaserExtractionRate.of_uniformVolumeGrowth K h.stride_pos ?_
  intro η hη
  obtain ⟨r, count, m, n, p, hr, hcount, hm, hn, hp, hdeg,
      hcopyLog, hxLog, hyLog, hzLog⟩ := h.extract η hη
  refine ⟨r, count, m, n, p, hr, hcount, hm, hn, hp, hdeg, hcopyLog, ?_⟩
  have hvolumeLog :
      Real.log ((m * n * p : ℕ) : ℝ) = Real.log m + Real.log n + Real.log p := by
    push_cast
    rw [Real.log_mul
        (mul_ne_zero (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne'))
        (by exact_mod_cast hp.ne'),
      Real.log_mul (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]
  rw [hvolumeLog]
  linarith

/-- Base-two specialization of `hasLaserExtractionRate`, in the coordinates used by numerical
laser certificates.

If one stride contains `stride` source tensors and its copy and side bases are respectively
`2^(stride*retained)`, `2^(stride*matrixX)`, `2^(stride*matrixY)`, and
`2^(stride*matrixZ)`, then the achieved logarithmic rate is

`log 2 * (retained + ω * (matrixX + matrixY + matrixZ) / 3)`.

Thus the theorem directly exposes rectangular-volume assembly rather than replacing the three
side exponents by their minimum. -/
theorem hasLaserExtractionRate_bits
    {T : Tensor3 K V} {stride : ℕ}
    {retained matrixX matrixY matrixZ : ℝ}
    (h : UniformLaserBaseExtraction K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ ((stride : ℝ) * matrixX))
      ((2 : ℝ) ^ ((stride : ℝ) * matrixY))
      ((2 : ℝ) ^ ((stride : ℝ) * matrixZ))) :
    HasLaserExtractionRate K T
      (Real.log 2 *
        (retained + omega K * ((matrixX + matrixY + matrixZ) / 3))) := by
  have hrate := h.hasLaserExtractionRate
  convert hrate using 1
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hstride : (stride : ℝ) ≠ 0 := by exact_mod_cast h.stride_pos.ne'
  field_simp [hstride]

end UniformLaserBaseExtraction

end Semiring

section Field

variable (K : Type u) [Field K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Any achieved extraction rate is bounded by the logarithm of the source tensor's constructive
border rank. -/
theorem HasLaserExtractionRate.le_log_borderRank
    {T : Tensor3 K V} {value : ℝ}
    (h : HasLaserExtractionRate K T value) :
    value ≤ Real.log (borderRank T) := by
  by_contra hvalue
  have hgap : 0 < value - Real.log (borderRank T) :=
    sub_pos.mpr (lt_of_not_ge hvalue)
  let ε := (value - Real.log (borderRank T)) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  rcases h ε hε with ⟨k, L, m, n, p, hk, hm, hn, hp, hdeg, hsum, hrate⟩
  have hasi := asymptoticSum_le_of_borderRankLE (ι := Fin L) K m n p
    ((borderRank_spec T).power k) hm hn hp hdeg
  have hlog :
      Real.log (asymptoticSum K m n p) ≤
        Real.log ((borderRank T ^ k : ℕ) : ℝ) :=
    Real.log_le_log hsum hasi
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hrate' := hrate.trans hlog
  have hk_real : (0 : ℝ) < k := by exact_mod_cast hk
  dsimp [ε] at hrate'
  nlinarith

end Field

end AlgebraicComplexity
