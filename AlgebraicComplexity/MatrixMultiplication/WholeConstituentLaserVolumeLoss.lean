/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SubexponentialVolumeLoss
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume

/-!
# Whole-constituent assembly with subexponential volume loss

A whole-constituent cleanup produces an exact finite restriction to equal rectangular
matrix-multiplication tensors.  Method-of-types constructions generally control both the number
of copies and their integral volume only up to positive subexponential factors.  This module
packages those two estimates without weakening the finite tensor statement.

`WholeConstituentLaserVolumeLossSequenceData` is the direct constructor interface: its `stage`
field contains the exact restriction, while `copy_growth` and `volume_growth` contain the two
independent asymptotic estimates.  The conversion theorem computes the complete
`SubexponentialLaserVolumeLossSequence`; no assembled tensor degeneration is accepted as a
hypothesis.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- Whole-constituent finite stages together with independent subexponential losses in copy count
and rectangular volume. -/
structure WholeConstituentLaserVolumeLossSequenceData
    (T : Tensor3 K Source) (stride : ℕ) (copyBase volumeBase : ℝ) where
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
  stage : ∀ r, 0 < r →
    WholeConstituentLaserVolumeStage K (Tensor.power T (stride * r))
      (count r) (xSize r) (ySize r) (zSize r)
  copy_growth : ∀ r, 0 < r →
    copyBase ^ r ≤ copyLoss r * (count r : ℝ)
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤
      volumeLoss r * (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace WholeConstituentLaserVolumeLossSequenceData

/-- The exact whole-constituent stages and their two directed growth estimates form the standard
subexponential-volume-loss extraction interface. -/
noncomputable def toSubexponentialLaserVolumeLossSequence
    {T : Tensor3 K Source} {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : WholeConstituentLaserVolumeLossSequenceData K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeLossSequence K T stride copyBase volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := data.copyBase_pos
  volumeBase_pos := data.volumeBase_pos
  copyLoss := data.copyLoss
  volumeLoss := data.volumeLoss
  count := data.count
  xSize := data.xSize
  ySize := data.ySize
  zSize := data.zSize
  copyLoss_subexponential := data.copyLoss_subexponential
  volumeLoss_subexponential := data.volumeLoss_subexponential
  copyLoss_pos := data.copyLoss_pos
  volumeLoss_pos := data.volumeLoss_pos
  count_pos := data.count_pos
  xSize_pos := data.xSize_pos
  ySize_pos := data.ySize_pos
  zSize_pos := data.zSize_pos
  extract := fun r hr ↦ (data.stage r hr).polynomialDegenerates
  copy_growth := data.copy_growth
  volume_growth := data.volume_growth

end WholeConstituentLaserVolumeLossSequenceData

namespace WholeConstituentLaserVolumeSequenceData

/-- An exact-volume whole-constituent sequence is the special case with constant volume loss
`1`.  This adapter keeps existing clients on the more precise interface while allowing uniform
downstream use of the loss-aware endpoint. -/
noncomputable def toVolumeLossSequenceData
    {T : Tensor3 K Source} {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : WholeConstituentLaserVolumeSequenceData K T stride copyBase volumeBase) :
    WholeConstituentLaserVolumeLossSequenceData K T stride copyBase volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := data.copyBase_pos
  volumeBase_pos := data.volumeBase_pos
  copyLoss := data.loss
  volumeLoss := fun _ ↦ 1
  count := data.count
  xSize := data.xSize
  ySize := data.ySize
  zSize := data.zSize
  copyLoss_subexponential := data.loss_subexponential
  volumeLoss_subexponential := by
    simpa using Growth.Subexponential.natCast_pow 0
  copyLoss_pos := data.loss_pos
  volumeLoss_pos := by intro; norm_num
  count_pos := data.count_pos
  xSize_pos := data.xSize_pos
  ySize_pos := data.ySize_pos
  zSize_pos := data.zSize_pos
  stage := data.stage
  copy_growth := data.copy_growth
  volume_growth := by
    intro r hr
    simpa using data.volume_growth r hr

end WholeConstituentLaserVolumeSequenceData

end AlgebraicComplexity
