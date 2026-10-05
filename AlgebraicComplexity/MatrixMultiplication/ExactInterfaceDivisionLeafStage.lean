/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionStage

/-!
# Leaf stages for exact interface-division trees

Finite cleanup theorems often conclude that a whole-constituent stage is nonempty, whereas the
exact division-tree fold stores the chosen stage in `WholeConstituentLaserVolumeStage.Packed`.
This module supplies that local bridge.  It also constructs the canonical one-copy
`1 \times 1 \times 1` stage for a zero-multiplicity leaf.

Both constructions are leaf-local.  In particular, neither accepts a restriction of an assembled
source product: nonempty stages already contain their own source restriction, and the zero leaf is
proved directly from the canonical zeroth tensor power.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace WholeConstituentLaserVolumeStage.Packed

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Choose and pack a locally proved whole-constituent stage.

The four numerical outputs remain explicit in the input type.  Thus this operation hides no
cardinality or tensor-semantic premise; it only eliminates `Nonempty`. -/
noncomputable def ofNonempty
    {source : Tensor3 K V} {copies xSize ySize zSize : ℕ}
    (stage : Nonempty (WholeConstituentLaserVolumeStage.{u, v, z}
      K source copies xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage.Packed.{u, v, z} K source where
  copies := copies
  xSize := xSize
  ySize := ySize
  zSize := zSize
  stage := Classical.choice stage

end WholeConstituentLaserVolumeStage.Packed

namespace WholeConstituentLaserVolumeStage

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- A zeroth tensor power restricts to the scalar matrix-multiplication tensor
`\langle 1,1,1\rangle`. -/
theorem powerZero_restricts_matrixMultiplicationOne (T : Tensor3 K V) :
    Restricts (Tensor.power T 0) (matrixMultiplication (K := K) 1 1 1) := by
  let collapse : ∀ c, PowerSpace K V 0 c →ₗ[K] MMSpace K 1 1 1 c :=
    fun c ↦ LinearMap.pi fun _ ↦
      (powerZeroScalarEquiv (K := K) (V := V) c).toLinearMap
  refine ⟨collapse, ?_⟩
  rw [Tensor.power_zero, Tensor.map_pure, matrixMultiplication]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  congr 1
  funext c
  cases c <;> funext ij <;> rcases ij with ⟨i, j⟩ <;>
    fin_cases i <;> fin_cases j <;>
    simp [collapse, mmTermOfTriple, mmTerm]

/-- The canonical one-copy `1 \times 1 \times 1` stage on a zeroth tensor power. -/
noncomputable def powerZero (T : Tensor3 K V) :
    WholeConstituentLaserVolumeStage.{u, max u v, z} K (Tensor.power T 0) 1 1 1 1 where
  I := PUnit.{z + 1}
  card_I := by simp
  source_restricts := by
    simpa only [matrixMultiplicationDirectSum] using
      (powerZero_restricts_matrixMultiplicationOne K T).trans
        (Tensor.Isomorphic.indexedDirectSum_unique (K := K) (ι := PUnit.{z + 1})
          (matrixMultiplication (K := K) 1 1 1)).symm.restricts

/-- Packed form of the canonical zeroth-power stage. -/
noncomputable def Packed.powerZero (T : Tensor3 K V) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u v, z} K (Tensor.power T 0) where
  copies := 1
  xSize := 1
  ySize := 1
  zSize := 1
  stage := WholeConstituentLaserVolumeStage.powerZero K T

end WholeConstituentLaserVolumeStage

namespace ExactInterfaceTermDivisionTree.LeafStages

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Turn a locally proved stage into the checked leaf consumed by the exact division-tree fold. -/
noncomputable def ofNonempty
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    {term : ExactInterfaceTermParameters depth}
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term)
    {copies xSize ySize zSize : ℕ}
    (stage : Nonempty (WholeConstituentLaserVolumeStage.{u, max u (max v w), z} K
      (P.exactInterfaceTermPowerRestriction encode multiplicityCase).target
      copies xSize ySize zSize)) :
    ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z}
      K P encode (.leaf multiplicityCase) :=
  .leaf multiplicityCase
    (WholeConstituentLaserVolumeStage.Packed.ofNonempty K stage)

/-- A zero-multiplicity regional leaf is discharged canonically by the tensor unit. -/
noncomputable def zero
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    {term : ExactInterfaceTermParameters depth}
    (hmultiplicity : term.multiplicity = 0) :
    ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z}
      K P encode (.leaf (.zero hmultiplicity)) := by
  refine .leaf (.zero hmultiplicity) ?_
  exact WholeConstituentLaserVolumeStage.Packed.powerZero K P.realize

end ExactInterfaceTermDivisionTree.LeafStages

end AlgebraicComplexity
