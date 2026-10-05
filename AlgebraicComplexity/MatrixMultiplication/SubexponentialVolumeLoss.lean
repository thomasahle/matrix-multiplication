/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.CopyGrowth
import AlgebraicComplexity.MatrixMultiplication.LaserVolume

/-!
# Absorbing subexponential loss from rectangular volume

Method-of-types extractions naturally bound both the number of retained copies and the integral
volume of each retained matrix-multiplication tensor only up to subexponential factors.  The
standard `SubexponentialLaserVolumeSequence` already absorbs a copy-count loss, but requires the
volume inequality with no finite loss at every repetition.

This module supplies the symmetric interface.  A
`SubexponentialLaserVolumeLossSequence` carries separate positive subexponential losses for copy
count and output volume.  For every strictly smaller positive volume base, its main theorem gives
the existing `UniformLaserVolumeBaseExtraction` at the same stride and copy base.

The proof is finite and one-sided.  The existing copy-growth lemma gives a cutoff beyond which the
smaller volume base is realized by the actual natural-valued volume.  The copy-loss logarithm is
then absorbed at one explicitly chosen repetition beyond that cutoff.  No limit, root, or rounded
matrix dimension enters the argument.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

namespace Growth.Subexponential

/-- A positive subexponential loss has logarithm at most `eta * r` at some positive repetition
past any prescribed cutoff.

This is the tail-strengthened form of
`SubexponentialLaserVolumeSequence.exists_pos_log_loss_le_mul`. -/
theorem exists_ge_pos_log_le_mul
    {loss : ℕ → ℝ} (hloss : Growth.Subexponential loss)
    (hlossPos : ∀ r, 0 < r → 0 < loss r)
    {eta : ℝ} (heta : 0 < eta) (cutoff : ℕ) :
    ∃ r : ℕ, cutoff ≤ r ∧ 0 < r ∧ Real.log (loss r) ≤ (r : ℝ) * eta := by
  let delta : ℝ := Real.exp (eta / 2)
  have hdelta : 1 < delta := by
    dsimp [delta]
    rw [Real.one_lt_exp_iff]
    linarith
  obtain ⟨C, hC, hbound⟩ := hloss.2 delta hdelta
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (2 * Real.log C / eta)
  let r := max cutoff (N + 1)
  have hcutoff : cutoff ≤ r := Nat.le_max_left _ _
  have hNr : N ≤ r := by
    exact (Nat.le_succ N).trans (Nat.le_max_right cutoff (N + 1))
  have hr : 0 < r := by
    have : 0 < N + 1 := Nat.succ_pos N
    exact this.trans_le (Nat.le_max_right cutoff (N + 1))
  have hlogC : Real.log C ≤ (r : ℝ) * (eta / 2) := by
    have hNcast : 2 * Real.log C / eta ≤ (N : ℝ) := hN
    have hNleR : (N : ℝ) ≤ (r : ℝ) := by exact_mod_cast hNr
    have hetaNonzero : eta ≠ 0 := heta.ne'
    have hboundR := hNcast.trans hNleR
    field_simp [hetaNonzero] at hboundR ⊢
    nlinarith
  have hlossUpper := hbound r
  have hlossLog :
      Real.log (loss r) ≤ Real.log C + (r : ℝ) * Real.log delta := by
    calc
      Real.log (loss r) ≤ Real.log (C * delta ^ r) :=
        Real.log_le_log (hlossPos r hr) hlossUpper
      _ = Real.log C + (r : ℝ) * Real.log delta := by
        rw [Real.log_mul hC.ne' (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hdelta))),
          Real.log_pow]
  have hlogDelta : Real.log delta = eta / 2 := by
    dsimp [delta]
    rw [Real.log_exp]
  refine ⟨r, hcutoff, hr, ?_⟩
  rw [hlogDelta] at hlossLog
  exact hlossLog.trans (by nlinarith [hlogC])

end Growth.Subexponential

section Semiring

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Finite uniform extractions with separate subexponential losses in copy count and integral
rectangular volume. -/
structure SubexponentialLaserVolumeLossSequence (T : Tensor3 K V)
    (stride : ℕ) (copyBase volumeBase : ℝ) where
  stride_pos : 0 < stride
  copyBase_pos : 0 < copyBase
  volumeBase_pos : 0 < volumeBase
  copyLoss : ℕ → ℝ
  volumeLoss : ℕ → ℝ
  count : ℕ → ℕ
  xSize : ℕ → ℕ
  ySize : ℕ → ℕ
  zSize : ℕ → ℕ
  copyLoss_subexponential : Growth.Subexponential copyLoss
  volumeLoss_subexponential : Growth.Subexponential volumeLoss
  copyLoss_pos : ∀ r, 0 < r → 0 < copyLoss r
  volumeLoss_pos : ∀ r, 0 < r → 0 < volumeLoss r
  count_pos : ∀ r, 0 < r → 0 < count r
  xSize_pos : ∀ r, 0 < r → 0 < xSize r
  ySize_pos : ∀ r, 0 < r → 0 < ySize r
  zSize_pos : ∀ r, 0 < r → 0 < zSize r
  extract : ∀ r, 0 < r →
    PolynomialDegenerates (Tensor.power T (stride * r))
      (matrixMultiplicationDirectSum (ι := Fin (count r)) K
        (fun _ ↦ xSize r) (fun _ ↦ ySize r) (fun _ ↦ zSize r))
  copy_growth : ∀ r, 0 < r →
    copyBase ^ r ≤ copyLoss r * (count r : ℝ)
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤
      volumeLoss r * (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace SubexponentialLaserVolumeLossSequence

/-- Absorb both finite losses, retaining the exact copy base and any strictly smaller positive
volume base. -/
theorem toUniformLaserVolumeBaseExtraction
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase lowerVolumeBase : ℝ}
    (h : SubexponentialLaserVolumeLossSequence K T stride copyBase volumeBase)
    (hlowerPos : 0 < lowerVolumeBase) (hlower : lowerVolumeBase < volumeBase) :
    UniformLaserVolumeBaseExtraction K T stride copyBase lowerVolumeBase := by
  obtain ⟨cutoff, hvolumeTail⟩ :=
    h.volumeLoss_subexponential.exists_forall_pow_le_natCast_of_pow_le_mul
      hlowerPos hlower
  refine ⟨h.stride_pos, h.copyBase_pos, hlowerPos, ?_⟩
  intro eta heta
  obtain ⟨r, hcutoff, hr, hcopyLossLog⟩ :=
    h.copyLoss_subexponential.exists_ge_pos_log_le_mul h.copyLoss_pos heta cutoff
  have hvolume :
      lowerVolumeBase ^ r ≤
        (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) :=
    hvolumeTail r (h.xSize r * h.ySize r * h.zSize r) hcutoff
      (h.volume_growth r hr)
  refine ⟨r, h.count r, h.xSize r, h.ySize r, h.zSize r, hr,
    h.count_pos r hr, h.xSize_pos r hr, h.ySize_pos r hr, h.zSize_pos r hr,
    h.extract r hr, ?_, ?_⟩
  · have hcopyLog :
        Real.log (copyBase ^ r) ≤
          Real.log (h.copyLoss r * (h.count r : ℝ)) :=
      Real.log_le_log (pow_pos h.copyBase_pos r) (h.copy_growth r hr)
    rw [Real.log_pow,
      Real.log_mul (h.copyLoss_pos r hr).ne'
        (by exact_mod_cast (h.count_pos r hr).ne')] at hcopyLog
    nlinarith
  · have hvolumeLog :
        Real.log (lowerVolumeBase ^ r) ≤
          Real.log (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) :=
      Real.log_le_log (pow_pos hlowerPos r) hvolume
    rwa [Real.log_pow] at hvolumeLog

/-- Direct laser-rate consequence with a strictly backed-off volume base. -/
theorem hasLaserExtractionRate
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase lowerVolumeBase : ℝ}
    (h : SubexponentialLaserVolumeLossSequence K T stride copyBase volumeBase)
    (hlowerPos : 0 < lowerVolumeBase) (hlower : lowerVolumeBase < volumeBase) :
    HasLaserExtractionRate K T
      ((Real.log copyBase + (omega K / 3) * Real.log lowerVolumeBase) / stride) :=
  UniformLaserVolumeBaseExtraction.hasLaserExtractionRate K
    (toUniformLaserVolumeBaseExtraction K h hlowerPos hlower)

/-- Base-two rate consequence after backing the mean rectangular side exponent off strictly.

The input sequence may lose a positive subexponential factor from the *integral volume*.  Thus its
nominal exponent `volume` need not be attained at any prescribed finite repetition.  Every
strictly smaller positive exponent `lowerVolume` is nevertheless attained by the uniform laser
interface and contributes exactly `omega * lowerVolume` to the base-two rate. -/
theorem hasLaserExtractionRate_bits
    {T : Tensor3 K V} {stride : ℕ} {retained volume lowerVolume : ℝ}
    (h : SubexponentialLaserVolumeLossSequence K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hlower : lowerVolume < volume) :
    HasLaserExtractionRate K T
      (Real.log 2 * (retained + omega K * lowerVolume)) := by
  apply UniformLaserVolumeBaseExtraction.hasLaserExtractionRate_bits K
  apply h.toUniformLaserVolumeBaseExtraction K
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have hstride : (0 : ℝ) < stride := by exact_mod_cast h.stride_pos
    nlinarith

end SubexponentialLaserVolumeLossSequence

end Semiring
end AlgebraicComplexity
