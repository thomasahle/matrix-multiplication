/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.EventualWholeConstituentLaserVolumeLoss
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionStage
import AlgebraicComplexity.MatrixMultiplication.FiniteLaserVolumePower

/-!
# Eventual sequences assembled from exact interface-division trees

`ExactInterfaceTermDivisionTree.LeafStages.toPowerPacked` derives a whole-constituent stage from
one checked stage at every leaf of a finite recursive division tree.  Its source is the flat power
`P.realize ^ term.multiplicity`.  Certificate clients, however, normally expose their source in
blocked form `(P.realize ^ blockPower) ^ (stride * r)`.

This module supplies the missing power-coherence adapter and the corresponding tail-only sequence
constructor.  The constructor accepts only:

* a checked division tree and checked leaf stages at each sufficiently large repetition;
* the exact root-multiplicity identity;
* explicit subexponential copy and volume losses; and
* directed numerical growth inequalities for the outputs computed by the tree fold.

In particular, it does **not** accept a degeneration of the assembled source to the assembled
matrix-multiplication family.  That degeneration is derived by the existing division-tree fold and
canonical tensor-power coherence.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace ExactInterfaceTermDivisionTree.LeafStages

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Fold checked leaf stages and express the result on a blocked tensor power.

The restriction from the blocked source is the composite
`(P^blockPower)^repetitions ≅ P^(blockPower*repetitions) ≅ P^term.multiplicity`.
The recursive leaf product itself is still derived by `toPowerPacked`. -/
noncomputable def toBlockedPowerPacked
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    {term : ExactInterfaceTermParameters depth}
    {tree : ExactInterfaceTermDivisionTree term}
    (stages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree)
    (blockPower repetitions : ℕ)
    (hmultiplicity : term.multiplicity = blockPower * repetitions) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (Tensor.power (Tensor.power P.realize blockPower) repetitions) :=
  WholeConstituentLaserVolumeStage.Packed.precompose K
    ((Tensor.Isomorphic.power_power_mul_comm P.realize blockPower repetitions).restricts.trans
      (Tensor.Isomorphic.power_congr P.realize hmultiplicity.symm).restricts)
    stages.toPowerPacked

end ExactInterfaceTermDivisionTree.LeafStages

/-- Certificate-independent data for an eventual family of exact recursive division stages.

The four natural outputs are read from the checked tree fold itself.  Before `cutoff` (and at
repetition zero) the exported numerical functions use the harmless default `1`; no tensor stage is
postulated there. -/
structure EventualExactInterfaceDivisionStageData
    (K : Type u) [CommSemiring K]
    {depth : ℕ}
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type (max u v)}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (blockPower stride : ℕ) (copyBase volumeBase : ℝ) where
  stride_pos : 0 < stride
  copyBase_pos : 0 < copyBase
  volumeBase_pos : 0 < volumeBase
  cutoff : ℕ
  term : ℕ → ExactInterfaceTermParameters depth
  tree : ∀ r, ExactInterfaceTermDivisionTree (term r)
  multiplicity_eq : ∀ r, (term r).multiplicity = blockPower * (stride * r)
  leafStages : ∀ r, cutoff ≤ r → 0 < r →
    ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode (tree r)
  copyLoss : ℕ → ℝ
  volumeLoss : ℕ → ℝ
  copyLoss_subexponential : Growth.Subexponential copyLoss
  volumeLoss_subexponential : Growth.Subexponential volumeLoss
  copyLoss_pos : ∀ r, 0 < r → 0 < copyLoss r
  copy_growth : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
    copyBase ^ r ≤ copyLoss r *
      (((leafStages r hcutoff hr).toBlockedPowerPacked K blockPower (stride * r)
        (multiplicity_eq r)).copies : ℝ)
  volume_growth : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
    volumeBase ^ r ≤ volumeLoss r *
      ((((leafStages r hcutoff hr).toBlockedPowerPacked K blockPower (stride * r)
          (multiplicity_eq r)).xSize *
        ((leafStages r hcutoff hr).toBlockedPowerPacked K blockPower (stride * r)
          (multiplicity_eq r)).ySize *
        ((leafStages r hcutoff hr).toBlockedPowerPacked K blockPower (stride * r)
          (multiplicity_eq r)).zSize : ℕ) : ℝ)

namespace EventualExactInterfaceDivisionStageData

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}
variable {blockPower stride : ℕ} {copyBase volumeBase : ℝ}

/-- The checked, folded stage at one repetition in the valid tail. -/
noncomputable def packed
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (Tensor.power (Tensor.power P.realize blockPower) (stride * r)) :=
  (data.leafStages r hcutoff hr).toBlockedPowerPacked K blockPower (stride * r)
    (data.multiplicity_eq r)

/-- Copy count computed from the exact tree fold on the valid tail and set to `1` elsewhere. -/
noncomputable def count
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) (r : ℕ) : ℕ :=
  if hcutoff : data.cutoff ≤ r then
    if hr : 0 < r then (data.packed K r hcutoff hr).copies else 1
  else 1

/-- First matrix dimension computed from the exact tree fold on the valid tail. -/
noncomputable def xSize
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) (r : ℕ) : ℕ :=
  if hcutoff : data.cutoff ≤ r then
    if hr : 0 < r then (data.packed K r hcutoff hr).xSize else 1
  else 1

/-- Second matrix dimension computed from the exact tree fold on the valid tail. -/
noncomputable def ySize
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) (r : ℕ) : ℕ :=
  if hcutoff : data.cutoff ≤ r then
    if hr : 0 < r then (data.packed K r hcutoff hr).ySize else 1
  else 1

/-- Third matrix dimension computed from the exact tree fold on the valid tail. -/
noncomputable def zSize
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) (r : ℕ) : ℕ :=
  if hcutoff : data.cutoff ≤ r then
    if hr : 0 < r then (data.packed K r hcutoff hr).zSize else 1
  else 1

@[simp] theorem count_eq_packed
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    data.count K r = (data.packed K r hcutoff hr).copies := by
  simp only [count, dif_pos hcutoff, dif_pos hr]

@[simp] theorem xSize_eq_packed
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    data.xSize K r = (data.packed K r hcutoff hr).xSize := by
  simp only [xSize, dif_pos hcutoff, dif_pos hr]

@[simp] theorem ySize_eq_packed
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    data.ySize K r = (data.packed K r hcutoff hr).ySize := by
  simp only [ySize, dif_pos hcutoff, dif_pos hr]

@[simp] theorem zSize_eq_packed
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    data.zSize K r = (data.packed K r hcutoff hr).zSize := by
  simp only [zSize, dif_pos hcutoff, dif_pos hr]

/-- Exact recursive division data form a tail-only whole-constituent sequence.

Positivity of the computed count and dimensions is derived from the positive exponential bases
and the directed growth inequalities; it is not an extra certificate premise. -/
noncomputable def toEventualWholeConstituentLaserVolumeLossData
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) :
    EventualWholeConstituentLaserVolumeLossData K
      (Tensor.power P.realize blockPower) stride copyBase volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := data.copyBase_pos
  volumeBase_pos := data.volumeBase_pos
  cutoff := data.cutoff
  copyLoss := data.copyLoss
  volumeLoss := data.volumeLoss
  count := data.count K
  xSize := data.xSize K
  ySize := data.ySize K
  zSize := data.zSize K
  copyLoss_subexponential := data.copyLoss_subexponential
  volumeLoss_subexponential := data.volumeLoss_subexponential
  copyLoss_pos := data.copyLoss_pos
  count_pos := by
    intro r hcutoff hr
    have hpositive : 0 < data.copyLoss r * ((data.packed K r hcutoff hr).copies : ℝ) :=
      (pow_pos data.copyBase_pos r).trans_le (data.copy_growth r hcutoff hr)
    rw [data.count_eq_packed K r hcutoff hr]
    by_contra hnot
    have hzero : (data.packed K r hcutoff hr).copies = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, Nat.cast_zero, mul_zero] at hpositive
    exact (lt_irrefl (0 : ℝ)) hpositive
  xSize_pos := by
    intro r hcutoff hr
    have hpositive : 0 < data.volumeLoss r *
        ((((data.packed K r hcutoff hr).xSize * (data.packed K r hcutoff hr).ySize *
          (data.packed K r hcutoff hr).zSize : ℕ) : ℝ)) :=
      (pow_pos data.volumeBase_pos r).trans_le (data.volume_growth r hcutoff hr)
    rw [data.xSize_eq_packed K r hcutoff hr]
    by_contra hnot
    have hzero : (data.packed K r hcutoff hr).xSize = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, zero_mul, Nat.cast_zero, mul_zero] at hpositive
    exact (lt_irrefl (0 : ℝ)) hpositive
  ySize_pos := by
    intro r hcutoff hr
    have hpositive : 0 < data.volumeLoss r *
        ((((data.packed K r hcutoff hr).xSize * (data.packed K r hcutoff hr).ySize *
          (data.packed K r hcutoff hr).zSize : ℕ) : ℝ)) :=
      (pow_pos data.volumeBase_pos r).trans_le (data.volume_growth r hcutoff hr)
    rw [data.ySize_eq_packed K r hcutoff hr]
    by_contra hnot
    have hzero : (data.packed K r hcutoff hr).ySize = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, mul_zero, zero_mul, Nat.cast_zero] at hpositive
    exact (lt_irrefl (0 : ℝ)) hpositive
  zSize_pos := by
    intro r hcutoff hr
    have hpositive : 0 < data.volumeLoss r *
        ((((data.packed K r hcutoff hr).xSize * (data.packed K r hcutoff hr).ySize *
          (data.packed K r hcutoff hr).zSize : ℕ) : ℝ)) :=
      (pow_pos data.volumeBase_pos r).trans_le (data.volume_growth r hcutoff hr)
    rw [data.zSize_eq_packed K r hcutoff hr]
    by_contra hnot
    have hzero : (data.packed K r hcutoff hr).zSize = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, mul_zero, Nat.cast_zero, mul_zero] at hpositive
    exact (lt_irrefl (0 : ℝ)) hpositive
  stage := by
    intro r hcutoff hr
    simpa only [data.count_eq_packed K r hcutoff hr,
      data.xSize_eq_packed K r hcutoff hr,
      data.ySize_eq_packed K r hcutoff hr,
      data.zSize_eq_packed K r hcutoff hr] using
        (data.packed K r hcutoff hr).stage.toFin
  copy_growth := by
    intro r hcutoff hr
    simpa only [packed, data.count_eq_packed K r hcutoff hr] using
      data.copy_growth r hcutoff hr
  volume_growth := by
    intro r hcutoff hr
    simpa only [packed, data.xSize_eq_packed K r hcutoff hr,
      data.ySize_eq_packed K r hcutoff hr,
      data.zSize_eq_packed K r hcutoff hr] using
        data.volume_growth r hcutoff hr

end EventualExactInterfaceDivisionStageData

end AlgebraicComplexity
