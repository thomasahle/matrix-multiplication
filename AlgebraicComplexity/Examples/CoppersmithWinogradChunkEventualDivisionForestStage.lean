/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradInterfaceCore
import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AlgebraicComplexity.MatrixMultiplication.EventualExactInterfaceDivisionForestStage
import AlgebraicComplexity.MatrixMultiplication.EventualWholeConstituentLaserVolumeTransport

/-!
# Transporting eventual CW chunk-division *forests* to the honest source

This is the forest analogue of
`AlgebraicComplexity/Examples/CoppersmithWinogradChunkEventualDivisionStage.lean`.  A single exact
division tree has one fixed root constituent index; a complete laser-method stage selects several
root types from disjoint source segments and multiplies them externally.
`EventualExactInterfaceDivisionForestStageData` is the interface that folds such a nonempty family,
and it exports the same tail-native whole-constituent data at `Tensor.power P.realize blockPower`.

The recursive interface construction treats one depth-`depth` CW chunk as its source tensor, so the
division `blockPower` is again `1`: one blocked factor is one chunk.  One chunk represents exactly
`2 ^ depth` base Coppersmith--Winograd tensors, but that is an isomorphism rather than definitional
equality, so the source transport is packaged here, once, after the forest has been folded.

The exported eventual family therefore has honest source `CW_q^(2 ^ depth)`.  At depth three this
is `CW_q^8`, so a stage at stride `38` and repetition `r` consumes exactly `8 * (38 * r) = 304 * r`
base CW letters — the invariant recorded as
`MatrixMultiplication.TotalWeightEndpointComposition.sourceLetters_eq`.

Nothing here is specific to a certificate: the forest, all recursive stages, both losses and all
four directed growth inequalities come from `data`.  The only new ingredient is the canonical chunk
isomorphism followed by first-power coherence.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Transport an eventual exact division *forest* family on one depth-`depth` CW chunk per block to
the honest source tensor `CW_q^(2 ^ depth)`.

All recursive stages and all numerical data come from `data`; source transport uses the generic
eventual-family precomposition theorem along the canonical chunk isomorphism. -/
noncomputable def cwChunkEventualDivisionForestStageData_toCWPower
    (K : Type u) [CommRing K] (q depth : ℕ)
    {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : EventualExactInterfaceDivisionForestStageData
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
noncomputable def cwDepthThreeEventualDivisionForestStageData_toCWPowerEight
    (K : Type u) [CommRing K] (q : ℕ)
    {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : EventualExactInterfaceDivisionForestStageData
      K (cwChunkPartitionedTensor K q 3) (fun _c ↦ cwChunkSplitWord 3)
      1 stride copyBase volumeBase) :
    EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power (coppersmithWinograd K q) 8)
      stride copyBase volumeBase := by
  have hpow : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [← hpow]
  exact cwChunkEventualDivisionForestStageData_toCWPower K q 3 data

end AlgebraicComplexity.Examples
