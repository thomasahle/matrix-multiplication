/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionLeafStage

set_option autoImplicit false

/-!
# Loss-aware volume budgets on exact interface-division trees

An exact interface-division tree assembles independently proved matrix-multiplication stages at
its leaves.  A method-of-types estimate for one leaf commonly has the form

```text
2 ^ leafBudget <= leafLoss * (xSize * ySize * zSize).
```

Budgets add and losses multiply when two child stages are externally multiplied.  This module
records that elementary calculus once, independently of any tensor family or numerical
certificate.

`foldLeafBudget` and `foldLeafLoss` perform the two folds over the division tree.
`LeafStages.MeetsVolumeBudgetWithLoss` insists on the finite inequality separately at every leaf,
so a forest-level estimate cannot be inserted as an unexplained premise.  The main theorem then
derives the corresponding inequality for the exact stage produced by `LeafStages.toPacked`.

Nothing here proves a loss subexponential or constructs a tensor restriction: those belong to the
client's asymptotic layer and to the existing exact leaf-stage assembly, respectively.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace ExactInterfaceTermDivisionTree

/-- Add a real-valued leaf budget over an exact interface-division tree. -/
noncomputable def foldLeafBudget {depth : ℕ}
    (leafBudget : ExactInterfaceTermParameters depth → ℝ) :
    {term : ExactInterfaceTermParameters depth} →
      ExactInterfaceTermDivisionTree term → ℝ
  | term, .leaf _ => leafBudget term
  | _, .branch _ left right =>
      foldLeafBudget leafBudget left + foldLeafBudget leafBudget right

@[simp] theorem foldLeafBudget_leaf {depth : ℕ}
    (leafBudget : ExactInterfaceTermParameters depth → ℝ)
    {term : ExactInterfaceTermParameters depth}
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term) :
    foldLeafBudget leafBudget (.leaf multiplicityCase) = leafBudget term := rfl

@[simp] theorem foldLeafBudget_branch {depth : ℕ}
    (leafBudget : ExactInterfaceTermParameters depth → ℝ)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (left : ExactInterfaceTermDivisionTree division.leftTerm)
    (right : ExactInterfaceTermDivisionTree division.rightTerm) :
    foldLeafBudget leafBudget (.branch division left right) =
      foldLeafBudget leafBudget left + foldLeafBudget leafBudget right := rfl

/-- Multiply a real-valued leaf loss over an exact interface-division tree. -/
noncomputable def foldLeafLoss {depth : ℕ}
    (leafLoss : ExactInterfaceTermParameters depth → ℝ) :
    {term : ExactInterfaceTermParameters depth} →
      ExactInterfaceTermDivisionTree term → ℝ
  | term, .leaf _ => leafLoss term
  | _, .branch _ left right =>
      foldLeafLoss leafLoss left * foldLeafLoss leafLoss right

@[simp] theorem foldLeafLoss_leaf {depth : ℕ}
    (leafLoss : ExactInterfaceTermParameters depth → ℝ)
    {term : ExactInterfaceTermParameters depth}
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term) :
    foldLeafLoss leafLoss (.leaf multiplicityCase) = leafLoss term := rfl

@[simp] theorem foldLeafLoss_branch {depth : ℕ}
    (leafLoss : ExactInterfaceTermParameters depth → ℝ)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (left : ExactInterfaceTermDivisionTree division.leftTerm)
    (right : ExactInterfaceTermDivisionTree division.rightTerm) :
    foldLeafLoss leafLoss (.branch division left right) =
      foldLeafLoss leafLoss left * foldLeafLoss leafLoss right := rfl

namespace LeafStages

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}

/-- Every leaf stage realizes its assigned bit budget up to its assigned multiplicative loss.

This is deliberately recursive rather than one inequality on the assembled stage.  In
particular, a client must connect each local loss to the same local stage that carries the tensor
semantics. -/
def MeetsVolumeBudgetWithLoss
    (leafBudget leafLoss : ExactInterfaceTermParameters depth → ℝ) :
    {term : ExactInterfaceTermParameters depth} →
      {tree : ExactInterfaceTermDivisionTree term} →
        ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree → Prop
  | term, _, .leaf _ packed =>
      (2 : ℝ) ^ leafBudget term ≤
        leafLoss term * ((packed.xSize * packed.ySize * packed.zSize : ℕ) : ℝ)
  | _, _, .branch _ leftStages rightStages =>
      MeetsVolumeBudgetWithLoss leafBudget leafLoss leftStages ∧
        MeetsVolumeBudgetWithLoss leafBudget leafLoss rightStages

@[simp] theorem meetsVolumeBudgetWithLoss_leaf
    (leafBudget leafLoss : ExactInterfaceTermParameters depth → ℝ)
    {term : ExactInterfaceTermParameters depth}
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term)
    (packed : WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (P.exactInterfaceTermPowerRestriction encode multiplicityCase).target) :
    MeetsVolumeBudgetWithLoss K leafBudget leafLoss
        (ExactInterfaceTermDivisionTree.LeafStages.leaf multiplicityCase packed) ↔
      (2 : ℝ) ^ leafBudget term ≤
        leafLoss term * ((packed.xSize * packed.ySize * packed.zSize : ℕ) : ℝ) :=
  Iff.rfl

@[simp] theorem meetsVolumeBudgetWithLoss_branch
    (leafBudget leafLoss : ExactInterfaceTermParameters depth → ℝ)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    {left : ExactInterfaceTermDivisionTree division.leftTerm}
    {right : ExactInterfaceTermDivisionTree division.rightTerm}
    (leftStages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode left)
    (rightStages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode right) :
    MeetsVolumeBudgetWithLoss K leafBudget leafLoss
        (ExactInterfaceTermDivisionTree.LeafStages.branch division leftStages rightStages) ↔
      MeetsVolumeBudgetWithLoss K leafBudget leafLoss leftStages ∧
        MeetsVolumeBudgetWithLoss K leafBudget leafLoss rightStages :=
  Iff.rfl

/-- Leaf-local lossy volume bounds multiply through the exact division-tree stage.

Proof sketch: at a branch, `Real.rpow_add` turns the sum of the two bit budgets into a product.
Multiply the two induction hypotheses, reassociate the two leaf losses, and use the definitional
dimension law of `WholeConstituentLaserVolumeStage.Packed.external`. -/
theorem two_rpow_foldLeafBudget_le_foldLeafLoss_mul_toPacked
    (leafBudget leafLoss : ExactInterfaceTermParameters depth → ℝ)
    {term : ExactInterfaceTermParameters depth}
    {tree : ExactInterfaceTermDivisionTree term}
    (stages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree)
    (hstages : MeetsVolumeBudgetWithLoss K leafBudget leafLoss stages) :
    (2 : ℝ) ^ foldLeafBudget leafBudget tree ≤
      foldLeafLoss leafLoss tree *
        ((stages.toPacked.xSize * stages.toPacked.ySize * stages.toPacked.zSize : ℕ) : ℝ) := by
  induction stages with
  | @leaf leafTerm multiplicityCase packed => exact hstages
  | @branch parent division left right leftStages rightStages ihleft ihright =>
      obtain ⟨hleft, hright⟩ := hstages
      have hl := ihleft hleft
      have hr := ihright hright
      have hbase : (0 : ℝ) < 2 := by norm_num
      have hleftNonneg :
          0 ≤ foldLeafLoss leafLoss left *
            ((leftStages.toPacked.xSize * leftStages.toPacked.ySize *
              leftStages.toPacked.zSize : ℕ) : ℝ) :=
        (Real.rpow_nonneg hbase.le _).trans hl
      rw [foldLeafBudget_branch, foldLeafLoss_branch, Real.rpow_add hbase]
      have hcast :
          ((ExactInterfaceTermDivisionTree.LeafStages.branch division leftStages
                  rightStages).toPacked.xSize *
              (ExactInterfaceTermDivisionTree.LeafStages.branch division leftStages
                  rightStages).toPacked.ySize *
              (ExactInterfaceTermDivisionTree.LeafStages.branch division leftStages
                  rightStages).toPacked.zSize : ℕ) =
            (leftStages.toPacked.xSize * leftStages.toPacked.ySize *
                leftStages.toPacked.zSize) *
              (rightStages.toPacked.xSize * rightStages.toPacked.ySize *
                rightStages.toPacked.zSize) := by
        show (leftStages.toPacked.xSize * rightStages.toPacked.xSize) *
            (leftStages.toPacked.ySize * rightStages.toPacked.ySize) *
            (leftStages.toPacked.zSize * rightStages.toPacked.zSize) = _
        ring
      rw [hcast, Nat.cast_mul]
      calc
        (2 : ℝ) ^ foldLeafBudget leafBudget left *
            (2 : ℝ) ^ foldLeafBudget leafBudget right ≤
          (foldLeafLoss leafLoss left *
              ((leftStages.toPacked.xSize * leftStages.toPacked.ySize *
                leftStages.toPacked.zSize : ℕ) : ℝ)) *
            (foldLeafLoss leafLoss right *
              ((rightStages.toPacked.xSize * rightStages.toPacked.ySize *
                rightStages.toPacked.zSize : ℕ) : ℝ)) :=
          mul_le_mul hl hr (Real.rpow_nonneg hbase.le _) hleftNonneg
        _ = (foldLeafLoss leafLoss left * foldLeafLoss leafLoss right) *
            (((leftStages.toPacked.xSize * leftStages.toPacked.ySize *
                leftStages.toPacked.zSize : ℕ) : ℝ) *
              ((rightStages.toPacked.xSize * rightStages.toPacked.ySize *
                rightStages.toPacked.zSize : ℕ) : ℝ)) := by
          ring

/-- Precomposing the assembled stage with the proved division-tree restriction preserves all
three dimensions, so the same lossy bound holds on `LeafStages.toPowerPacked`. -/
theorem two_rpow_foldLeafBudget_le_foldLeafLoss_mul_toPowerPacked
    (leafBudget leafLoss : ExactInterfaceTermParameters depth → ℝ)
    {term : ExactInterfaceTermParameters depth}
    {tree : ExactInterfaceTermDivisionTree term}
    (stages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree)
    (hstages : MeetsVolumeBudgetWithLoss K leafBudget leafLoss stages) :
    (2 : ℝ) ^ foldLeafBudget leafBudget tree ≤
      foldLeafLoss leafLoss tree *
        ((stages.toPowerPacked.xSize * stages.toPowerPacked.ySize *
          stages.toPowerPacked.zSize : ℕ) : ℝ) :=
  two_rpow_foldLeafBudget_le_foldLeafLoss_mul_toPacked
    K leafBudget leafLoss stages hstages

end LeafStages
end ExactInterfaceTermDivisionTree
end AlgebraicComplexity
