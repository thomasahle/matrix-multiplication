/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.PairedTotalWeightA5Row

set_option autoImplicit false

/-!
# Executable constructor for frozen paired total-weight rows

The replacement witness supplies three positive categorical factor tables.  Logical `X` and `Y`
are total functions on `Fin 9`.  A relevant boundary category is an unordered pair of valid slots;
the witness stores its factor at the smaller certificate-order slot, while `none` carries the
pooled interior factor.  Unreachable unordered pairs may use any positive default.

The b32 count row is not serialized again.  It is defined from the supplied b20 top table by the
exact `2^12` rescaling, so its alignment theorem is definitional.  Positive parent mass proves
positive b32 profile mass.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace MatrixMultiplication.PairedTotalWeightA5FrozenRowData

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.Tensor
open MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDual
open MatrixMultiplication.PairedTotalWeightA5Row
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

noncomputable section

/-- Smaller certificate-order representative of an unordered pair of valid slots. -/
def minValidSlot
    {parent : Fin positiveLevelFourShapeCount}
    (left right : LevelFourValidSlot parent) : Fin levelFourPairSlotCount :=
  ⟨min left.1.val right.1.val,
    lt_of_le_of_lt (min_le_left _ _) left.1.isLt⟩

theorem minValidSlot_comm
    {parent : Fin positiveLevelFourShapeCount}
    (left right : LevelFourValidSlot parent) :
    minValidSlot left right = minValidSlot right left := by
  apply Fin.ext
  exact min_comm _ _

/-- Extend certificate-order boundary-orbit factors to every unordered valid-slot pair.

Only categories produced by `levelFourA5BoundaryCategory` enter the checker form.  The total
extension nevertheless stays positive on arbitrary `Sym2` inputs. -/
def boundaryFactor
    {parent : Fin positiveLevelFourShapeCount}
    (boundaryMinFactor : Fin levelFourPairSlotCount → ℕ)
    (interiorFactor : ℕ) : LevelFourA5BoundaryCategory parent → ℕ
  | none => interiorFactor
  | some orbit =>
      Sym2.lift
        ⟨fun left right ↦ boundaryMinFactor (minValidSlot left right),
          fun left right ↦ congrArg boundaryMinFactor (minValidSlot_comm left right)⟩
        orbit

theorem boundaryFactor_pos
    {parent : Fin positiveLevelFourShapeCount}
    (boundaryMinFactor : Fin levelFourPairSlotCount → ℕ)
    (interiorFactor : ℕ)
    (hboundary : ∀ slot, 0 < boundaryMinFactor slot)
    (hinterior : 0 < interiorFactor) :
    ∀ boundary, 0 < boundaryFactor (parent := parent)
      boundaryMinFactor interiorFactor boundary := by
  intro boundary
  cases boundary with
  | none => exact hinterior
  | some orbit =>
      refine Sym2.inductionOn orbit ?_
      intro left right
      exact hboundary (minValidSlot left right)

/-- Parent-independent frozen categorical factors for one manifest row. -/
structure Factors where
  xFactor : LevelFourA5Coordinate → ℕ
  yFactor : LevelFourA5Coordinate → ℕ
  boundaryMinFactor : Fin levelFourPairSlotCount → ℕ
  interiorFactor : ℕ
  xFactor_pos : ∀ x, 0 < xFactor x
  yFactor_pos : ∀ y, 0 < yFactor y
  boundaryMinFactor_pos : ∀ slot, 0 < boundaryMinFactor slot
  interiorFactor_pos : 0 < interiorFactor

/-- Positive categorical weights assembled from total coordinate and boundary factor functions. -/
def weights
    (parent : Fin positiveLevelFourShapeCount)
    (xFactor yFactor : LevelFourA5Coordinate → ℕ)
    (boundaryMinFactor : Fin levelFourPairSlotCount → ℕ)
    (interiorFactor : ℕ)
    (hx : ∀ x, 0 < xFactor x)
    (hy : ∀ y, 0 < yFactor y)
    (hboundary : ∀ slot, 0 < boundaryMinFactor slot)
    (hinterior : 0 < interiorFactor) :
    CategoricalIntegerWeights parent xzy where
  xFactor := xFactor
  yFactor := yFactor
  boundaryFactor := boundaryFactor boundaryMinFactor interiorFactor
  xFactor_pos := hx
  yFactor_pos := hy
  boundaryFactor_pos :=
    boundaryFactor_pos boundaryMinFactor interiorFactor hboundary hinterior

namespace Factors

/-- Interpret frozen factors on the dependent categorical alphabet of a positive parent. -/
def toWeights (data : Factors) (parent : Fin positiveLevelFourShapeCount) :
    CategoricalIntegerWeights parent xzy :=
  weights parent data.xFactor data.yFactor data.boundaryMinFactor data.interiorFactor
    data.xFactor_pos data.yFactor_pos data.boundaryMinFactor_pos data.interiorFactor_pos

end Factors

/-- The frozen width-32 count row derived from the replacement b20 top table. -/
def count32
    (top : TopBranchRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) : ℕ :=
  levelFourSlotNumerator top region region parent slot *
    AlgebraicComplexity.dyadicDenominator 12

@[simp] theorem count32_eq_top
    (top : TopBranchRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (slot : LevelFourValidSlot parent) :
    count32 top region parent slot =
      levelFourSlotNumerator top region region parent slot *
        AlgebraicComplexity.dyadicDenominator 12 :=
  rfl

/-- Rescaling the derived b32 row by `2^84` recovers the literal occurrence-parent mass. -/
theorem profileMass_count32_mul_dyadicDenominator84
    (top : TopBranchRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) :
    WordType.profileMass (count32 top region parent) *
        AlgebraicComplexity.dyadicDenominator 84 =
      levelFourParentSamples top region region parent := by
  rw [← profileMass_levelFourOccurrenceSourceProfile]
  simp only [WordType.profileMass, count32, levelFourOccurrenceSourceProfile]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro slot _
  rw [levelFourChildSamples_sq_eq_dyadicScales]
  exact Nat.mul_assoc _ _ _

/-- Positive parent mass implies positive mass of the derived b32 row. -/
theorem profileMass_count32_pos
    (top : TopBranchRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hparent : 0 < levelFourParentSamples top region region parent) :
    0 < WordType.profileMass (count32 top region parent) := by
  have hproduct :
      0 < WordType.profileMass (count32 top region parent) *
        AlgebraicComplexity.dyadicDenominator 84 := by
    rw [profileMass_count32_mul_dyadicDenominator84]
    exact hparent
  exact Nat.pos_of_mul_pos_right hproduct

/-- Construct one exact replacement row from its active key and categorical factor functions. -/
def row
    (top : TopBranchRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hparent : 0 < levelFourParentSamples top region region parent)
    (xFactor yFactor : LevelFourA5Coordinate → ℕ)
    (boundaryMinFactor : Fin levelFourPairSlotCount → ℕ)
    (interiorFactor : ℕ)
    (hx : ∀ x, 0 < xFactor x)
    (hy : ∀ y, 0 < yFactor y)
    (hboundary : ∀ slot, 0 < boundaryMinFactor slot)
    (hinterior : 0 < interiorFactor) : Row top where
  region := region
  parent := parent
  count32 := count32 top region parent
  count32_eq_top := count32_eq_top top region parent
  count32Mass_pos := profileMass_count32_pos top region parent hparent
  weights := weights parent xFactor yFactor boundaryMinFactor interiorFactor
    hx hy hboundary hinterior

/-- Convenience constructor from one frozen factor record. -/
def Factors.toRow
    (data : Factors)
    (top : TopBranchRows) (region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (hparent : 0 < levelFourParentSamples top region region parent) : Row top where
  region := region
  parent := parent
  count32 := count32 top region parent
  count32_eq_top := count32_eq_top top region parent
  count32Mass_pos := profileMass_count32_pos top region parent hparent
  weights := data.toWeights parent

end

end MatrixMultiplication.PairedTotalWeightA5FrozenRowData
