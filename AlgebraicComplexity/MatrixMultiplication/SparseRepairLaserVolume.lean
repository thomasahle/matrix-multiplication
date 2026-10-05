/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SparseRepairCounting
import AlgebraicComplexity.MatrixMultiplication.LaserVolume

/-!
# Candidate-independent sparse-repair laser-volume assembly

This file packages the last reusable step between finite compatibility cleanup and the
volume-native laser endpoint.  A stage retains the exact finite data needed for verification:

* an indexed family of cleaned fibers modeled as damaged copies of one partitioned tensor;
* aggregate hole-incidence bounds and the assertion that their three budgets use at most half
  of the retained fixed-type class;
* a one-sided supply bound for the requested number of complete repair trees;
* the source restriction and the intact typed-leaf matrix-multiplication restriction.

The finite theorem constructs the repaired matrix-multiplication direct sum.  A sequence of such
stages, together with one-sided copy-count and rectangular-volume growth bounds, is then exactly
a `SubexponentialLaserVolumeSequence`.  No numerical certificate values occur in this module.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity.Tensor

universe u

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {I : Type u} [Fintype I] [DecidableEq I]
variable {U : Leg → Type u}
variable [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
variable {family : I → Tensor3 K U}

namespace ModeledFiberFamily

/-- If the three aggregate dense-fiber budgets use at most half the retained family, then at
least half of that family is simultaneously sparse on all three tensor legs. -/
theorem card_le_two_mul_card_sparseIndices_of_halfDensity
    (model : ModeledFiberFamily P family) (base : ℕ) (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 * ∑ i : I, (model.holes i c).card ≤
        budget c * Fintype.card (A c))
    (hhalf : 2 * (budget .X + budget .Y + budget .Z) ≤ Fintype.card I) :
    Fintype.card I ≤ 2 * (model.sparseIndices base).card := by
  have hcover := model.card_le_card_sparseIndices_add_budgets base budget haggregate
  omega

/-- Aggregate incidence, half density, and a division-free repair-supply inequality produce a
finite direct sum of identical rectangular matrix-multiplication tensors.

The two factors `2` have distinct meanings in the hypotheses: `hhalf` says that dense-fiber
budgets remove at most half the fixed-type class, while `hsupply` asks that the requested complete
repair supplies fit in that surviving half. -/
theorem degenerate_matrixMultiplicationDirectSum_of_aggregate_halfDensity
    (model : ModeledFiberFamily P family)
    {Relabel : Type u} [Fintype Relabel] [DecidableEq Relabel] [Nonempty Relabel]
    (relabelings : UniformStructureRelabelings (G := Relabel) P)
    {O : Type u} [Fintype O] [DecidableEq O]
    {base : ℕ} (hbase : 1 < base)
    (target : ∀ c, Finset (A c))
    (budget : Leg → ℕ)
    (haggregate : ∀ c,
      base * 4 * ∑ i : I, (model.holes i c).card ≤
        budget c * Fintype.card (A c))
    (hhalf : 2 * (budget .X + budget .Y + budget .Z) ≤ Fintype.card I)
    (hsupply :
      2 * (Fintype.card O *
        sevenBranchBudget (logarithmicRepairDepth base target)) ≤ Fintype.card I)
    {Source : Leg → Type u}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {T : Tensor3 K Source}
    (hfamily : Restricts T (Tensor.indexedDirectSum family))
    {m n p : ℕ}
    (hleaf : Restricts (P.box target).realize
      (matrixMultiplication (K := K) m n p)) :
    PolynomialDegenerates T
      (matrixMultiplicationDirectSum (ι := O) K
        (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p)) := by
  have hclass := model.card_le_two_mul_card_sparseIndices_of_halfDensity
    base budget haggregate hhalf
  have hrepairCount :
      Fintype.card O * sevenBranchBudget (logarithmicRepairDepth base target) ≤
        (model.sparseIndices base).card := by
    omega
  exact model.degenerate_matrixMultiplicationDirectSum relabelings hbase
    (logarithmicRepairDepth base target) target le_rfl hrepairCount hfamily hleaf

end ModeledFiberFamily

end AlgebraicComplexity.HoleRepair

namespace AlgebraicComplexity

open Tensor

/-! ## A finite sparse-repair extraction witness -/

universe u

section FiniteStage

variable (K : Type) [CommSemiring K]
variable {Source : Leg → Type}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- All semantic and finite counting data for one positive proportional repetition.

The auxiliary types deliberately live in `Type`: this matches the concrete CW block models and
lets the output index be literally `Fin copies`, as required by `SubexponentialLaserVolumeSequence`.
No asymptotic estimate is stored here. -/
structure SparseRepairLaserVolumeStage
    (source : Tensor3 K Source) (copies xSize ySize zSize : ℕ) where
  A : Leg → Type
  [fintypeA : ∀ c, Fintype (A c)]
  [decidableEqA : ∀ c, DecidableEq (A c)]
  V : ∀ c, A c → Type
  [addCommMonoidV : ∀ c a, AddCommMonoid (V c a)]
  [moduleV : ∀ c a, Module K (V c a)]
  P : PartitionedTensor (K := K) (A := A) V
  I : Type
  [fintypeI : Fintype I]
  [decidableEqI : DecidableEq I]
  U : Leg → Type
  [addCommMonoidU : ∀ c, AddCommMonoid (U c)]
  [moduleU : ∀ c, Module K (U c)]
  family : I → Tensor3 K U
  model : HoleRepair.ModeledFiberFamily P family
  Relabel : Type
  [fintypeRelabel : Fintype Relabel]
  [decidableEqRelabel : DecidableEq Relabel]
  [nonemptyRelabel : Nonempty Relabel]
  relabelings : HoleRepair.UniformStructureRelabelings (G := Relabel) P
  base : ℕ
  base_gt_one : 1 < base
  target : ∀ c, Finset (A c)
  budget : Leg → ℕ
  aggregate : ∀ c,
    base * 4 * ∑ i : I, (model.holes i c).card ≤
      budget c * Fintype.card (A c)
  half_density :
    2 * (budget .X + budget .Y + budget .Z) ≤ Fintype.card I
  repair_supply :
    2 * (copies * HoleRepair.sevenBranchBudget
      (HoleRepair.logarithmicRepairDepth base target)) ≤ Fintype.card I
  source_restricts : Restricts source (Tensor.indexedDirectSum family)
  typedLeaf : Restricts (P.box target).realize
    (matrixMultiplication (K := K) xSize ySize zSize)

namespace SparseRepairLaserVolumeStage

/-- A verified finite sparse-repair stage yields the exact direct-sum degeneration expected by
the laser-volume endpoint. -/
theorem polynomialDegenerates
    {source : Tensor3 K Source} {copies xSize ySize zSize : ℕ}
    (stage : SparseRepairLaserVolumeStage K source copies xSize ySize zSize) :
    PolynomialDegenerates source
      (matrixMultiplicationDirectSum (ι := Fin copies) K
        (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize)) := by
  letI := stage.fintypeA
  letI := stage.decidableEqA
  letI := stage.addCommMonoidV
  letI := stage.moduleV
  letI := stage.fintypeI
  letI := stage.decidableEqI
  letI := stage.addCommMonoidU
  letI := stage.moduleU
  letI := stage.fintypeRelabel
  letI := stage.decidableEqRelabel
  letI := stage.nonemptyRelabel
  have hsupply :
      2 * (Fintype.card (Fin copies) * HoleRepair.sevenBranchBudget
        (HoleRepair.logarithmicRepairDepth stage.base stage.target)) ≤
        Fintype.card stage.I := by
    simpa only [Fintype.card_fin] using stage.repair_supply
  exact stage.model.degenerate_matrixMultiplicationDirectSum_of_aggregate_halfDensity
    (O := Fin copies)
    stage.relabelings stage.base_gt_one stage.target stage.budget stage.aggregate
      stage.half_density hsupply stage.source_restricts stage.typedLeaf

end SparseRepairLaserVolumeStage

end FiniteStage

/-! ## Candidate-neutral proportional sequence -/

section Sequence

variable (K : Type) [CommSemiring K]
variable {Source : Leg → Type}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- Candidate-independent input data for the final volume assembly.

All certificate-dependent quantities are parameters or proved fields.  In particular,
`copy_growth` is deliberately one-sided: a client may majorize every type-selection, hashing,
compatibility, and repair loss by any convenient positive subexponential function.  Likewise,
`volume_growth` needs only the product of the three typed-leaf dimensions. -/
structure SparseRepairLaserVolumeSequenceData
    (T : Tensor3 K Source) (stride : ℕ) (copyBase volumeBase : ℝ) where
  stride_pos : 0 < stride
  copyBase_pos : 0 < copyBase
  volumeBase_pos : 0 < volumeBase
  loss : ℕ → ℝ
  count : ℕ → ℕ
  xSize : ℕ → ℕ
  ySize : ℕ → ℕ
  zSize : ℕ → ℕ
  loss_subexponential : Growth.Subexponential loss
  loss_pos : ∀ r, 0 < r → 0 < loss r
  count_pos : ∀ r, 0 < r → 0 < count r
  xSize_pos : ∀ r, 0 < r → 0 < xSize r
  ySize_pos : ∀ r, 0 < r → 0 < ySize r
  zSize_pos : ∀ r, 0 < r → 0 < zSize r
  stage : ∀ r, 0 < r →
    SparseRepairLaserVolumeStage K (Tensor.power T (stride * r))
      (count r) (xSize r) (ySize r) (zSize r)
  copy_growth : ∀ r, 0 < r →
    copyBase ^ r ≤ loss r * (count r : ℝ)
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace SparseRepairLaserVolumeSequenceData

/-- The final reusable bridge: exact finite sparse-repair stages plus one-sided asymptotic growth
bounds form a `SubexponentialLaserVolumeSequence`. -/
noncomputable def toSubexponentialLaserVolumeSequence
    {T : Tensor3 K Source} {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : SparseRepairLaserVolumeSequenceData K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeSequence K T stride copyBase volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := data.copyBase_pos
  volumeBase_pos := data.volumeBase_pos
  loss := data.loss
  count := data.count
  xSize := data.xSize
  ySize := data.ySize
  zSize := data.zSize
  loss_subexponential := data.loss_subexponential
  loss_pos := data.loss_pos
  count_pos := data.count_pos
  xSize_pos := data.xSize_pos
  ySize_pos := data.ySize_pos
  zSize_pos := data.zSize_pos
  extract := fun r hr ↦ (data.stage r hr).polynomialDegenerates
  copy_growth := data.copy_growth
  volume_growth := data.volume_growth

end SparseRepairLaserVolumeSequenceData

end Sequence

end AlgebraicComplexity
