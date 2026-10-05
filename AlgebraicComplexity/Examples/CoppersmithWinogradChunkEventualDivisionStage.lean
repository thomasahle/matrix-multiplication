/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradInterfaceCore
import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AlgebraicComplexity.MatrixMultiplication.EventualExactInterfaceDivisionStage
import AlgebraicComplexity.MatrixMultiplication.EventualWholeConstituentLaserVolumeTransport

/-!
# Transporting eventual CW chunk-division stages to the honest source

The recursive interface construction treats one depth-`depth` CW chunk as its source tensor.  One
chunk represents exactly `2^depth` base Coppersmith--Winograd tensors, but this equality is an
isomorphism rather than definitional equality.  This module packages the source transport once,
after the exact division tree has been folded.

The division-stage `blockPower` is therefore `1`: one blocked factor is one chunk.  The exported
eventual family has honest source `CW_q^(2^depth)`.  At depth three this is `CW_q^8`, so a stage at
stride `38` and repetition `r` consumes exactly `8 * (38 * r) = 304r` base CW letters.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Transport an eventual exact division family on one depth-`depth` CW chunk per block to the
honest source tensor `CW_q^(2^depth)`.

All recursive stages and all numerical data come from `data`.  The only new ingredient is the
canonical chunk isomorphism followed by first-power coherence; source transport then uses the
generic eventual-family precomposition theorem. -/
noncomputable def cwChunkEventualDivisionStageData_toCWPower
    (K : Type u) [CommRing K] (q depth : ℕ)
    {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : EventualExactInterfaceDivisionStageData
      K (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth)
      1 stride copyBase volumeBase) :
    EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K q) (2 ^ depth))
      stride copyBase volumeBase := by
  have hchunk : Restricts
      (Tensor.power (coppersmithWinograd K q) (2 ^ depth))
      (cwChunkPartitionedTensor K q depth).realize :=
    (((cwPartitionedTensor_isomorphic K q).symm.power (2 ^ depth)).trans
      (cwChunkPartitionedTensor_isomorphic_power K q depth)).restricts
  have hsource : Restricts
      (Tensor.power (coppersmithWinograd K q) (2 ^ depth))
      (Tensor.power (cwChunkPartitionedTensor K q depth).realize 1) :=
    hchunk.trans
      (Tensor.Isomorphic.power_one
        (cwChunkPartitionedTensor K q depth).realize).symm.restricts
  exact EventualWholeConstituentLaserVolumeLossData.precompose K hsource
    (data.toEventualWholeConstituentLaserVolumeLossData K)

/-- Depth-three specialization: one recursive chunk is exactly eight base CW tensors. -/
noncomputable def cwDepthThreeEventualDivisionStageData_toCWPowerEight
    (K : Type u) [CommRing K] (q : ℕ)
    {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : EventualExactInterfaceDivisionStageData
      K (cwChunkPartitionedTensor K q 3) (fun _c ↦ cwChunkSplitWord 3)
      1 stride copyBase volumeBase) :
    EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K q) 8)
      stride copyBase volumeBase := by
  have hpow : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [← hpow]
  exact cwChunkEventualDivisionStageData_toCWPower K q 3 data

end AlgebraicComplexity.Examples
