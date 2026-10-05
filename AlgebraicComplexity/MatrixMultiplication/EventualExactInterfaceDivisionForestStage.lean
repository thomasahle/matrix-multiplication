/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.EventualExactInterfaceDivisionStage

/-!
# Eventual stages assembled from a nonempty forest of exact division trees

An exact regional-division tree has one fixed root constituent index.  A complete laser-method
stage normally uses several root constituent types, selected from disjoint source segments and
externally multiplied.  Treating that outer product as one division tree would be ill typed: a
binary regional division preserves its parent index.

This module supplies the missing outer layer.  `ExactInterfaceTermDivisionTree.Staged` packages
one checked tree and its checked leaf stages.  `Staged.positiveProduct` folds a nonempty family of
such packages directly from the corresponding flat source power.  Every root selection and every
recursive leaf-product restriction is therefore derived by the existing exact tree theorem.

`EventualExactInterfaceDivisionForestStageData` repeats that finite construction past a cutoff,
allows explicit subexponential copy and volume losses, and exports the existing tail-native
whole-constituent interface.  It has no field for a restriction of the assembled forest.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace WholeConstituentLaserVolumeStage.Packed

/-- Combine packed stages on two powers of the same tensor, using canonical power-add coherence.
Copy counts and all three dimensions multiply exactly. -/
noncomputable def powerAdd
    (K : Type u) [CommSemiring K]
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    {T : Tensor3 K V} {leftExponent rightExponent : ℕ}
    (left : WholeConstituentLaserVolumeStage.Packed.{u, max u v, z} K
      (Tensor.power T leftExponent))
    (right : WholeConstituentLaserVolumeStage.Packed.{u, max u v, z} K
      (Tensor.power T rightExponent)) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u v, z} K
      (Tensor.power T (leftExponent + rightExponent)) where
  copies := left.copies * right.copies
  xSize := left.xSize * right.xSize
  ySize := left.ySize * right.ySize
  zSize := left.zSize * right.zSize
  stage := WholeConstituentLaserVolumeStage.powerAdd K left.stage right.stage

end WholeConstituentLaserVolumeStage.Packed

namespace ExactInterfaceTermDivisionTree

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- One exact root term together with its recursively checked division tree and all leaf stages.

The tensor stage is stored only at the leaves.  In particular this package contains no
restriction from the root source power to its assembled output. -/
structure Staged
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) where
  term : ExactInterfaceTermParameters depth
  tree : ExactInterfaceTermDivisionTree term
  leafStages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree

namespace Staged

/-- Derive the checked stage of one root tree from its source power. -/
noncomputable def toPowerPacked
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    (staged : ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (Tensor.power P.realize staged.term.multiplicity) :=
  staged.leafStages.toPowerPacked K

/-- Multiply a natural-valued statistic over a recursively represented nonempty word. -/
def positiveNatProduct {S : Type*} (value : S → ℕ) :
    (n : ℕ) → PositiveWord S n → ℕ
  | 0, entry => value entry
  | n + 1, entries => positiveNatProduct value n entries.1 * value entries.2

/-- Fold a nonempty family of checked root trees into one stage on the flat source power whose
exponent is the sum of their root multiplicities. -/
noncomputable def positiveProduct
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth} :
    (n : ℕ) →
      (stages : PositiveWord
        (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n) →
      WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
        (Tensor.power P.realize
          (positiveWordSum (fun staged ↦ staged.term.multiplicity) n stages))
  | 0, staged => staged.toPowerPacked K
  | n + 1, stages =>
      WholeConstituentLaserVolumeStage.Packed.powerAdd K
        (positiveProduct n stages.1) (stages.2.toPowerPacked K)

@[simp] theorem positiveProduct_copies
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n) :
    (positiveProduct K n stages).copies =
      positiveNatProduct (fun staged ↦ (staged.toPowerPacked K).copies) n stages := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (positiveProduct K n stages.1).copies *
          (stages.2.toPowerPacked K).copies = _
      rw [ih]
      rfl

@[simp] theorem positiveProduct_xSize
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n) :
    (positiveProduct K n stages).xSize =
      positiveNatProduct (fun staged ↦ (staged.toPowerPacked K).xSize) n stages := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (positiveProduct K n stages.1).xSize *
          (stages.2.toPowerPacked K).xSize = _
      rw [ih]
      rfl

@[simp] theorem positiveProduct_ySize
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n) :
    (positiveProduct K n stages).ySize =
      positiveNatProduct (fun staged ↦ (staged.toPowerPacked K).ySize) n stages := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (positiveProduct K n stages.1).ySize *
          (stages.2.toPowerPacked K).ySize = _
      rw [ih]
      rfl

@[simp] theorem positiveProduct_zSize
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n) :
    (positiveProduct K n stages).zSize =
      positiveNatProduct (fun staged ↦ (staged.toPowerPacked K).zSize) n stages := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (positiveProduct K n stages.1).zSize *
          (stages.2.toPowerPacked K).zSize = _
      rw [ih]
      rfl

/-- Fold a nonempty forest and express its flat source power as a blocked tensor power. -/
noncomputable def positiveProductToBlockedPowerPacked
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    {n blockPower repetitions : ℕ}
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n)
    (hmultiplicity :
      positiveWordSum (fun staged ↦ staged.term.multiplicity) n stages =
        blockPower * repetitions) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (Tensor.power (Tensor.power P.realize blockPower) repetitions) :=
  WholeConstituentLaserVolumeStage.Packed.precompose K
    ((Tensor.Isomorphic.power_power_mul_comm P.realize blockPower repetitions).restricts.trans
      (Tensor.Isomorphic.power_congr P.realize hmultiplicity.symm).restricts)
    (positiveProduct K n stages)

end Staged
end ExactInterfaceTermDivisionTree

/-- Tail-native data for a nonempty forest of independently indexed exact division trees.

The forest itself supplies every assembled stage.  The remaining fields are only source-exponent
bookkeeping and directed numerical growth bounds for the four outputs computed by that fold. -/
structure EventualExactInterfaceDivisionForestStageData
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
  rootCount : ℕ
  forest : ∀ r, cutoff ≤ r → 0 < r →
    PositiveWord (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) rootCount
  multiplicity_eq : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
    positiveWordSum (fun staged ↦ staged.term.multiplicity) rootCount
      (forest r hcutoff hr) = blockPower * (stride * r)
  copyLoss : ℕ → ℝ
  volumeLoss : ℕ → ℝ
  copyLoss_subexponential : Growth.Subexponential copyLoss
  volumeLoss_subexponential : Growth.Subexponential volumeLoss
  copyLoss_pos : ∀ r, 0 < r → 0 < copyLoss r
  copy_growth : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
    copyBase ^ r ≤ copyLoss r *
      (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
        (forest r hcutoff hr) (multiplicity_eq r hcutoff hr)).copies : ℕ) : ℝ)
  volume_growth : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
    volumeBase ^ r ≤ volumeLoss r *
      (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
          (forest r hcutoff hr) (multiplicity_eq r hcutoff hr)).xSize *
        (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
          (forest r hcutoff hr) (multiplicity_eq r hcutoff hr)).ySize *
        (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
          (forest r hcutoff hr) (multiplicity_eq r hcutoff hr)).zSize : ℕ) : ℝ)

namespace EventualExactInterfaceDivisionForestStageData

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}
variable {blockPower stride : ℕ} {copyBase volumeBase : ℝ}

/-- The exact forest fold on one valid tail repetition. -/
noncomputable def packed
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (Tensor.power (Tensor.power P.realize blockPower) (stride * r)) :=
  ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
    (data.forest r hcutoff hr) (data.multiplicity_eq r hcutoff hr)

/-- Copy count of the checked forest fold, with a harmless default outside its tail. -/
noncomputable def count
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) (r : ℕ) : ℕ :=
  if hcutoff : data.cutoff ≤ r then
    if hr : 0 < r then (data.packed K r hcutoff hr).copies else 1
  else 1

/-- First dimension of the checked forest fold. -/
noncomputable def xSize
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) (r : ℕ) : ℕ :=
  if hcutoff : data.cutoff ≤ r then
    if hr : 0 < r then (data.packed K r hcutoff hr).xSize else 1
  else 1

/-- Second dimension of the checked forest fold. -/
noncomputable def ySize
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) (r : ℕ) : ℕ :=
  if hcutoff : data.cutoff ≤ r then
    if hr : 0 < r then (data.packed K r hcutoff hr).ySize else 1
  else 1

/-- Third dimension of the checked forest fold. -/
noncomputable def zSize
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) (r : ℕ) : ℕ :=
  if hcutoff : data.cutoff ≤ r then
    if hr : 0 < r then (data.packed K r hcutoff hr).zSize else 1
  else 1

@[simp] theorem count_eq_packed
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    data.count K r = (data.packed K r hcutoff hr).copies := by
  simp only [count, dif_pos hcutoff, dif_pos hr]

@[simp] theorem xSize_eq_packed
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    data.xSize K r = (data.packed K r hcutoff hr).xSize := by
  simp only [xSize, dif_pos hcutoff, dif_pos hr]

@[simp] theorem ySize_eq_packed
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    data.ySize K r = (data.packed K r hcutoff hr).ySize := by
  simp only [ySize, dif_pos hcutoff, dif_pos hr]

@[simp] theorem zSize_eq_packed
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase)
    (r : ℕ) (hcutoff : data.cutoff ≤ r) (hr : 0 < r) :
    data.zSize K r = (data.packed K r hcutoff hr).zSize := by
  simp only [zSize, dif_pos hcutoff, dif_pos hr]

/-- A checked eventual forest gives the existing tail-native whole-constituent family.

All tensor semantics come from `positiveProductToBlockedPowerPacked`; positivity of the four
numeric outputs follows from the directed growth inequalities. -/
noncomputable def toEventualWholeConstituentLaserVolumeLossData
    (data : EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
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

end EventualExactInterfaceDivisionForestStageData

namespace EventualExactInterfaceDivisionStageData

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}
variable {blockPower stride : ℕ} {copyBase volumeBase : ℝ}

/-- Regard the existing one-tree eventual constructor as a singleton forest.

This is a semantic regression client for the forest API: at `rootCount = 0`, its fold is
definitionally the original checked tree fold and all numerical data are inherited unchanged. -/
noncomputable def toForest
    (data : EventualExactInterfaceDivisionStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase) :
    EventualExactInterfaceDivisionForestStageData.{u, v, w, z}
      K P encode blockPower stride copyBase volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := data.copyBase_pos
  volumeBase_pos := data.volumeBase_pos
  cutoff := data.cutoff
  rootCount := 0
  forest := fun r hcutoff hr ↦
    { term := data.term r
      tree := data.tree r
      leafStages := data.leafStages r hcutoff hr }
  multiplicity_eq := fun r _hcutoff _hr ↦ data.multiplicity_eq r
  copyLoss := data.copyLoss
  volumeLoss := data.volumeLoss
  copyLoss_subexponential := data.copyLoss_subexponential
  volumeLoss_subexponential := data.volumeLoss_subexponential
  copyLoss_pos := data.copyLoss_pos
  copy_growth := by
    intro r hcutoff hr
    simpa [EventualExactInterfaceDivisionForestStageData.packed,
      ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked,
      ExactInterfaceTermDivisionTree.Staged.positiveProduct,
      ExactInterfaceTermDivisionTree.Staged.toPowerPacked,
      WholeConstituentLaserVolumeStage.Packed.precompose,
      ExactInterfaceTermDivisionTree.LeafStages.toBlockedPowerPacked,
      EventualExactInterfaceDivisionStageData.packed] using
        data.copy_growth r hcutoff hr
  volume_growth := by
    intro r hcutoff hr
    simpa [EventualExactInterfaceDivisionForestStageData.packed,
      ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked,
      ExactInterfaceTermDivisionTree.Staged.positiveProduct,
      ExactInterfaceTermDivisionTree.Staged.toPowerPacked,
      WholeConstituentLaserVolumeStage.Packed.precompose,
      ExactInterfaceTermDivisionTree.LeafStages.toBlockedPowerPacked,
      EventualExactInterfaceDivisionStageData.packed] using
        data.volume_growth r hcutoff hr

end EventualExactInterfaceDivisionStageData

end AlgebraicComplexity
