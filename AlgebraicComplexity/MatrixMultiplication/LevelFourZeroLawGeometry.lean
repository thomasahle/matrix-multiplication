/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourShapeGeometry

/-!
# Finite zero-law geometry for level-four certificates

This dependency-light module reconstructs the exact row-dependent alphabets used by zero-law
tables.  Keeping finite shape geometry separate from probability arrays lets generated support
maps be checked without loading the full level-four reconstruction and entropy environment.
-/

namespace MatrixMultiplication.LevelFourRemainingReconstruction

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.LevelFourReconstruction.PositiveLevelThreeData

set_option maxRecDepth 100000

/-- Number of level-four zero shapes. -/
def zeroFourShapeCount : ℕ := 48

/-- Number of all level-three shape/region types. -/
def zeroThreeRowCount : ℕ := 270

/-- Number of words of length `length` over `{0,1,2}` with a prescribed digit sum.

This is the coefficient recurrence for `(1 + x + x²)^length`, and hence matches the support-table
widths in the archived evaluator. -/
def ternarySupportWidth : ℕ → ℕ → ℕ
  | 0, total => if total = 0 then 1 else 0
  | length + 1, total =>
      ternarySupportWidth length total +
        (if 1 ≤ total then ternarySupportWidth length (total - 1) else 0) +
        (if 2 ≤ total then ternarySupportWidth length (total - 2) else 0)

/-- Level-two support widths are bounded by the evaluator's padded width three. -/
theorem ternarySupportWidth_two_le_three (total : Fin 5) :
    ternarySupportWidth 2 total ≤ 3 := by
  decide +revert

/-- Level-three support widths are bounded by nineteen. -/
theorem ternarySupportWidth_four_le_nineteen (total : Fin 9) :
    ternarySupportWidth 4 total ≤ 19 := by
  decide +revert

/-- Level-four support widths are bounded by 1,107. -/
theorem ternarySupportWidth_eight_le_1107 (total : Fin 17) :
    ternarySupportWidth 8 total ≤ 1107 := by
  decide +revert

/-- The value stored by the evaluator as `zero*_total`: zero for a positive shape, and otherwise
the first positive coordinate after choosing the first zero coordinate. -/
def zeroLawTotal (shape : Shape) : ℕ :=
  if shape.IsPositive then 0
  else if 0 < shape.x then shape.x
  else if 0 < shape.y then shape.y
  else shape.z

/-- All forty-five shapes of coordinate sum eight. -/
theorem shapes_eight_length : (shapes 8).length = 45 := by
  decide

/-- All 153 shapes of coordinate sum sixteen. -/
theorem shapes_sixteen_length : (shapes 16).length = 153 := by
  decide

/-- Nonpositive level-four shapes, in the evaluator's order. -/
def zeroFourShapes : List Shape :=
  (shapes 16).filter fun shape ↦ decide (¬shape.IsPositive)

theorem zeroFourShapes_length : zeroFourShapes.length = zeroFourShapeCount := by
  decide

/-- Shape belonging to one of the 270 level-three shape/region rows. -/
def zeroThreeShape (row : Fin zeroThreeRowCount) : Shape :=
  (shapes 8)[row.val / regionCount]?.getD default

/-- Shape belonging to a level-four zero-law row. -/
def zeroFourShape (shape : Fin zeroFourShapeCount) : Shape :=
  zeroFourShapes[shape.val]?.getD default

theorem zeroThreeShape_mem (row : Fin zeroThreeRowCount) : zeroThreeShape row ∈ shapes 8 := by
  have hi : row.val / regionCount < (shapes 8).length := by
    rw [shapes_eight_length]
    have hr := row.isLt
    simp only [zeroThreeRowCount, regionCount] at hr ⊢
    omega
  unfold zeroThreeShape
  rw [List.getElem?_eq_getElem hi]
  exact List.getElem_mem (l := shapes 8) hi

theorem zeroThreeShape_total (row : Fin zeroThreeRowCount) :
    (zeroThreeShape row).total = 8 :=
  mem_shapes_total (zeroThreeShape_mem row)

theorem zeroFourShape_mem (shape : Fin zeroFourShapeCount) :
    zeroFourShape shape ∈ zeroFourShapes := by
  have hi : shape.val < zeroFourShapes.length := by
    rw [zeroFourShapes_length]
    exact shape.isLt
  unfold zeroFourShape
  rw [List.getElem?_eq_getElem hi]
  exact List.getElem_mem (l := zeroFourShapes) hi

theorem zeroFourShape_geometry (shape : Fin zeroFourShapeCount) :
    (zeroFourShape shape).total = 16 ∧ ¬(zeroFourShape shape).IsPositive := by
  have hmem := zeroFourShape_mem shape
  simp only [zeroFourShapes, List.mem_filter] at hmem
  exact ⟨mem_shapes_total hmem.1, of_decide_eq_true hmem.2⟩

/-- A valid level-two edge-zero row is indexed by a positive level-three node, decomposition
region, and one genuine split slot. -/
abbrev EdgeIndex :=
  Fin nodeCount × (Fin regionCount × Fin splitSlotCount)

abbrev EdgeZeroRow :=
  {index : EdgeIndex // splitSlotValid index.1 index.2.2}

def EdgeZeroRow.node (row : EdgeZeroRow) : Fin nodeCount := row.1.1

def EdgeZeroRow.region (row : EdgeZeroRow) : Fin regionCount := row.1.2.1

def EdgeZeroRow.slot (row : EdgeZeroRow) : Fin splitSlotCount := row.1.2.2

/-- Support width of one level-two edge zero law. -/
def edgeZeroWidth (row : EdgeZeroRow) : ℕ :=
  ternarySupportWidth 2 (zeroLawTotal (splitShape row.node row.slot))

/-- Support width of one level-three zero-law row. -/
def zeroThreeWidth (row : Fin zeroThreeRowCount) : ℕ :=
  ternarySupportWidth 4 (zeroLawTotal (zeroThreeShape row))

/-- A level-four zero row carries an incoming root region and a nonpositive shape. -/
abbrev ZeroFourRow := Fin regionCount × Fin zeroFourShapeCount

/-- Support width of one level-four zero-law row. -/
def zeroFourWidth (row : ZeroFourRow) : ℕ :=
  ternarySupportWidth 8 (zeroLawTotal (zeroFourShape row.2))

end MatrixMultiplication.LevelFourRemainingReconstruction
