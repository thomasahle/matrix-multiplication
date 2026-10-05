/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeLoss

/-!
# Eventual whole-constituent laser-volume families

An integral cleanup quotient may be zero at small repetitions and positive at every sufficiently
large repetition.  The laser method only needs arbitrarily large finite extractions, so requiring
a positive stage at every positive repetition adds an artificial finite-prefix obligation.

This file provides the tail-native interface.  It records exact whole-constituent stages only past
an explicit cutoff and absorbs separate subexponential copy and volume losses directly into
`UniformLaserVolumeBaseExtraction`.  No placeholder stage before the cutoff is constructed.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Semiring

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- Exact whole-constituent stages available after a finite cutoff, with separate
subexponential losses in copy count and integral rectangular volume.

The loss in the copy count is required to be positive at every positive repetition because its
logarithm is used to choose a large index.  Positivity and tensor semantics of the actual output
data are required only on the tail where the stages exist. -/
structure EventualWholeConstituentLaserVolumeLossData
    (T : Tensor3 K Source) (stride : ℕ) (copyBase volumeBase : ℝ) where
  stride_pos : 0 < stride
  copyBase_pos : 0 < copyBase
  volumeBase_pos : 0 < volumeBase
  cutoff : ℕ
  copyLoss : ℕ → ℝ
  volumeLoss : ℕ → ℝ
  count : ℕ → ℕ
  xSize : ℕ → ℕ
  ySize : ℕ → ℕ
  zSize : ℕ → ℕ
  copyLoss_subexponential : Growth.Subexponential copyLoss
  volumeLoss_subexponential : Growth.Subexponential volumeLoss
  copyLoss_pos : ∀ r, 0 < r → 0 < copyLoss r
  count_pos : ∀ r, cutoff ≤ r → 0 < r → 0 < count r
  xSize_pos : ∀ r, cutoff ≤ r → 0 < r → 0 < xSize r
  ySize_pos : ∀ r, cutoff ≤ r → 0 < r → 0 < ySize r
  zSize_pos : ∀ r, cutoff ≤ r → 0 < r → 0 < zSize r
  stage : ∀ r, cutoff ≤ r → 0 < r →
    WholeConstituentLaserVolumeStage K (Tensor.power T (stride * r))
      (count r) (xSize r) (ySize r) (zSize r)
  copy_growth : ∀ r, cutoff ≤ r → 0 < r →
    copyBase ^ r ≤ copyLoss r * (count r : ℝ)
  volume_growth : ∀ r, cutoff ≤ r → 0 < r →
    volumeBase ^ r ≤
      volumeLoss r * (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace WholeConstituentLaserVolumeLossSequenceData

/-- Every all-repetition whole-constituent sequence is an eventual family with cutoff zero.
This adapter is also a small semantic client showing that the tail interface is a conservative
generalization of the existing sequence interface. -/
noncomputable def toEventual
    {T : Tensor3 K Source} {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : WholeConstituentLaserVolumeLossSequenceData
      K T stride copyBase volumeBase) :
    EventualWholeConstituentLaserVolumeLossData K T stride copyBase volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := data.copyBase_pos
  volumeBase_pos := data.volumeBase_pos
  cutoff := 0
  copyLoss := data.copyLoss
  volumeLoss := data.volumeLoss
  count := data.count
  xSize := data.xSize
  ySize := data.ySize
  zSize := data.zSize
  copyLoss_subexponential := data.copyLoss_subexponential
  volumeLoss_subexponential := data.volumeLoss_subexponential
  copyLoss_pos := data.copyLoss_pos
  count_pos := fun r _ hr ↦ data.count_pos r hr
  xSize_pos := fun r _ hr ↦ data.xSize_pos r hr
  ySize_pos := fun r _ hr ↦ data.ySize_pos r hr
  zSize_pos := fun r _ hr ↦ data.zSize_pos r hr
  stage := fun r _ hr ↦ data.stage r hr
  copy_growth := fun r _ hr ↦ data.copy_growth r hr
  volume_growth := fun r _ hr ↦ data.volume_growth r hr

end WholeConstituentLaserVolumeLossSequenceData

namespace EventualWholeConstituentLaserVolumeLossData

/-- Tail stages suffice for the direct laser-volume interface.  The copy loss is absorbed at one
repetition beyond both the semantic cutoff and the volume-loss cutoff; consequently no statement
about a small repetition is needed. -/
noncomputable def toUniformLaserVolumeBaseExtraction
    {T : Tensor3 K Source} {stride : ℕ} {copyBase volumeBase lowerVolumeBase : ℝ}
    (data : EventualWholeConstituentLaserVolumeLossData
      K T stride copyBase volumeBase)
    (hlowerPos : 0 < lowerVolumeBase) (hlower : lowerVolumeBase < volumeBase) :
    UniformLaserVolumeBaseExtraction K T stride copyBase lowerVolumeBase := by
  obtain ⟨volumeCutoff, hvolumeTail⟩ :=
    data.volumeLoss_subexponential.exists_forall_pow_le_natCast_of_pow_le_mul
      hlowerPos hlower
  refine ⟨data.stride_pos, data.copyBase_pos, hlowerPos, ?_⟩
  intro eta heta
  obtain ⟨r, hrCutoff, hr, hcopyLossLog⟩ :=
    data.copyLoss_subexponential.exists_ge_pos_log_le_mul
      data.copyLoss_pos heta (max data.cutoff volumeCutoff)
  have hdataCutoff : data.cutoff ≤ r :=
    (Nat.le_max_left _ _).trans hrCutoff
  have hvolumeCutoff : volumeCutoff ≤ r :=
    (Nat.le_max_right _ _).trans hrCutoff
  have hvolume :
      lowerVolumeBase ^ r ≤
        (((data.xSize r * data.ySize r * data.zSize r : ℕ) : ℝ)) :=
    hvolumeTail r (data.xSize r * data.ySize r * data.zSize r) hvolumeCutoff
      (data.volume_growth r hdataCutoff hr)
  refine ⟨r, data.count r, data.xSize r, data.ySize r, data.zSize r, hr,
    data.count_pos r hdataCutoff hr, data.xSize_pos r hdataCutoff hr,
    data.ySize_pos r hdataCutoff hr, data.zSize_pos r hdataCutoff hr,
    (data.stage r hdataCutoff hr).polynomialDegenerates, ?_, ?_⟩
  · have hcopyLog :
        Real.log (copyBase ^ r) ≤
          Real.log (data.copyLoss r * (data.count r : ℝ)) :=
      Real.log_le_log (pow_pos data.copyBase_pos r)
        (data.copy_growth r hdataCutoff hr)
    rw [Real.log_pow,
      Real.log_mul (data.copyLoss_pos r hr).ne'
        (by exact_mod_cast (data.count_pos r hdataCutoff hr).ne')] at hcopyLog
    nlinarith
  · have hvolumeLog :
        Real.log (lowerVolumeBase ^ r) ≤
          Real.log (((data.xSize r * data.ySize r * data.zSize r : ℕ) : ℝ)) :=
      Real.log_le_log (pow_pos hlowerPos r) hvolume
    rwa [Real.log_pow] at hvolumeLog

/-- Direct laser-rate consequence of an eventual whole-constituent family. -/
theorem hasLaserExtractionRate
    {T : Tensor3 K Source} {stride : ℕ} {copyBase volumeBase lowerVolumeBase : ℝ}
    (data : EventualWholeConstituentLaserVolumeLossData
      K T stride copyBase volumeBase)
    (hlowerPos : 0 < lowerVolumeBase) (hlower : lowerVolumeBase < volumeBase) :
    HasLaserExtractionRate K T
      ((Real.log copyBase + (omega K / 3) * Real.log lowerVolumeBase) / stride) :=
  (data.toUniformLaserVolumeBaseExtraction K hlowerPos hlower).hasLaserExtractionRate

/-- Base-two rate form: the retained exponent is unchanged, while the nominal mean rectangular
side exponent is backed off strictly to absorb the integral-volume loss. -/
theorem hasLaserExtractionRate_bits
    {T : Tensor3 K Source} {stride : ℕ} {retained volume lowerVolume : ℝ}
    (data : EventualWholeConstituentLaserVolumeLossData K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume)))
    (hlower : lowerVolume < volume) :
    HasLaserExtractionRate K T
      (Real.log 2 * (retained + omega K * lowerVolume)) := by
  apply UniformLaserVolumeBaseExtraction.hasLaserExtractionRate_bits K
  apply data.toUniformLaserVolumeBaseExtraction K
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have hstride : (0 : ℝ) < stride := by exact_mod_cast data.stride_pos
    nlinarith

end EventualWholeConstituentLaserVolumeLossData

end Semiring

end AlgebraicComplexity
