/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TypeExtraction
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeAssembly

/-!
# Permuting finite whole-constituent stages

A cyclic permutation of a tensor source rotates the three dimensions of every extracted
matrix-multiplication tensor.  This module lifts the corresponding tensor isomorphisms to finite
`WholeConstituentLaserVolumeStage`s.

The dimension order is part of each theorem's type: `cycle` sends `(X,Y,Z)` to `(Z,X,Y)`, while
`cycle.symm` sends it to `(Y,Z,X)`.  The proof permutes the source restriction and then retypes
every summand of the target direct sum.  No numerical growth estimate or asymptotic argument is
used.
-/

namespace AlgebraicComplexity

open Tensor

universe u v z

namespace WholeConstituentLaserVolumeStage

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Rotate a finite whole stage forward.  The source is permuted by `cycle` and the rectangular
dimensions rotate from `(x,y,z)` to `(z,x,y)`. -/
noncomputable def permuteCycle
    {source : Tensor3 K V} {copies xSize ySize zSize : ℕ}
    (stage : WholeConstituentLaserVolumeStage.{u, v, z} K source
      copies xSize ySize zSize) :
    WholeConstituentLaserVolumeStage.{u, v, z} K (Tensor.permute cycle source)
      copies zSize xSize ySize := by
  letI := stage.fintypeI
  refine
    { I := stage.I
      card_I := stage.card_I
      source_restricts := ?_ }
  have hpermuted := stage.source_restricts.permute cycle
  have htarget : Restricts
      (Tensor.permute cycle
        (matrixMultiplicationDirectSum (ι := stage.I) K
          (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize)))
      (matrixMultiplicationDirectSum (ι := stage.I) K
        (fun _ ↦ zSize) (fun _ ↦ xSize) (fun _ ↦ ySize)) := by
    unfold matrixMultiplicationDirectSum
    rw [Tensor.permute_indexedDirectSum]
    exact (Tensor.Isomorphic.indexedDirectSum
      (fun _ ↦ Tensor.Isomorphic.matrixMultiplication_cycle
        (K := K) xSize ySize zSize)).restricts
  exact hpermuted.trans htarget

/-- Rotate a finite whole stage backward.  The source is permuted by `cycle.symm` and the
rectangular dimensions rotate from `(x,y,z)` to `(y,z,x)`. -/
noncomputable def permuteCycleSymm
    {source : Tensor3 K V} {copies xSize ySize zSize : ℕ}
    (stage : WholeConstituentLaserVolumeStage.{u, v, z} K source
      copies xSize ySize zSize) :
    WholeConstituentLaserVolumeStage.{u, v, z} K (Tensor.permute cycle.symm source)
      copies ySize zSize xSize := by
  letI := stage.fintypeI
  refine
    { I := stage.I
      card_I := stage.card_I
      source_restricts := ?_ }
  have hpermuted := stage.source_restricts.permute cycle.symm
  have htarget : Restricts
      (Tensor.permute cycle.symm
        (matrixMultiplicationDirectSum (ι := stage.I) K
          (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize)))
      (matrixMultiplicationDirectSum (ι := stage.I) K
        (fun _ ↦ ySize) (fun _ ↦ zSize) (fun _ ↦ xSize)) := by
    unfold matrixMultiplicationDirectSum
    rw [Tensor.permute_indexedDirectSum]
    exact (Tensor.Isomorphic.indexedDirectSum
      (fun _ ↦ Tensor.Isomorphic.matrixMultiplication_cycle_symm
        (K := K) xSize ySize zSize)).restricts
  exact hpermuted.trans htarget

end WholeConstituentLaserVolumeStage
end AlgebraicComplexity
