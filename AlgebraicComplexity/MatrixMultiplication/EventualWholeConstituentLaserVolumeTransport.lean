/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.EventualWholeConstituentLaserVolumeLoss

/-!
# Source transport for eventual whole-constituent families

An eventual extraction family is contravariant in its source tensor.  If `newSource` restricts to
`source`, then every checked stage on a power of `source` is also a checked stage on the
corresponding power of `newSource`.  Copy counts, matrix dimensions, losses, and directed growth
inequalities are unchanged.

This small adapter keeps source coherence outside certificate-specific constructions.  In
particular, a client can build a recursive extraction on a convenient partitioned realization and
then transport the resulting eventual family to the honest tensor used by an exponent theorem.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace EventualWholeConstituentLaserVolumeLossData

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v} {NewSource : Leg → Type w}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
variable [∀ c, AddCommMonoid (NewSource c)] [∀ c, Module K (NewSource c)]

/-- Precompose every tail stage with a fixed exact restriction of source tensors.

The restriction is powered separately at each repetition.  All numerical fields are inherited
verbatim, so the construction introduces no additional loss and changes neither the cutoff nor
the stride. -/
noncomputable def precompose
    {source : Tensor3 K Source} {newSource : Tensor3 K NewSource}
    {stride : ℕ} {copyBase volumeBase : ℝ}
    (hsource : Restricts newSource source)
    (data : EventualWholeConstituentLaserVolumeLossData
      K source stride copyBase volumeBase) :
    EventualWholeConstituentLaserVolumeLossData
      K newSource stride copyBase volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := data.copyBase_pos
  volumeBase_pos := data.volumeBase_pos
  cutoff := data.cutoff
  copyLoss := data.copyLoss
  volumeLoss := data.volumeLoss
  count := data.count
  xSize := data.xSize
  ySize := data.ySize
  zSize := data.zSize
  copyLoss_subexponential := data.copyLoss_subexponential
  volumeLoss_subexponential := data.volumeLoss_subexponential
  copyLoss_pos := data.copyLoss_pos
  count_pos := data.count_pos
  xSize_pos := data.xSize_pos
  ySize_pos := data.ySize_pos
  zSize_pos := data.zSize_pos
  stage := by
    intro r hcutoff hr
    let oldStage := data.stage r hcutoff hr
    exact
      { I := oldStage.I
        fintypeI := oldStage.fintypeI
        card_I := oldStage.card_I
        source_restricts := (hsource.power (stride * r)).trans oldStage.source_restricts }
  copy_growth := data.copy_growth
  volume_growth := data.volume_growth

end EventualWholeConstituentLaserVolumeLossData

end AlgebraicComplexity
