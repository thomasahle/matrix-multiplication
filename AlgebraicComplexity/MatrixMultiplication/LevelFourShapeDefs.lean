/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Init

/-!
# Definitions for finite recursive constituent shapes

This file contains only executable data and indexing definitions.  Proofs about the enumeration
live in `LevelFourShapeGeometry`, keeping generated certificate clients' import and elaboration
cost small.
-/

namespace AlgebraicComplexity.LevelFourReconstruction

/-- A three-coordinate constituent shape. -/
structure Shape where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Inhabited, Repr

namespace Shape

/-- Coordinate sum of a shape. -/
def total (s : Shape) : Nat := s.x + s.y + s.z

/-- All three coordinates are strictly positive. -/
def IsPositive (s : Shape) : Prop := 0 < s.x ∧ 0 < s.y ∧ 0 < s.z

/-- Coordinatewise containment, used to recognize a left child of a recursive split. -/
def Le (u s : Shape) : Prop := u.x ≤ s.x ∧ u.y ≤ s.y ∧ u.z ≤ s.z

/-- The coordinatewise complementary child. -/
def complement (s u : Shape) : Shape :=
  ⟨s.x - u.x, s.y - u.y, s.z - u.z⟩

instance : LE Shape := ⟨Le⟩

instance (s : Shape) : Decidable s.IsPositive := by
  change Decidable (0 < s.x ∧ 0 < s.y ∧ 0 < s.z)
  infer_instance

instance (u s : Shape) : Decidable (u ≤ s) := by
  change Decidable (u.x ≤ s.x ∧ u.y ≤ s.y ∧ u.z ≤ s.z)
  infer_instance

end Shape

/-- Lexicographically ordered triples of naturals with coordinate sum `total`. -/
def shapes (total : Nat) : List Shape :=
  (List.range (total + 1)).flatMap fun x ↦
    (List.range (total - x + 1)).map fun y ↦
      ⟨x, y, total - x - y⟩

/-- Positive shapes at the parent level of a recursive split. -/
def positiveShapes (total : Nat) : List Shape :=
  (shapes total).filter fun shape ↦ decide shape.IsPositive

/-- All level-three left-child splits of `parent`, in certificate order. -/
def levelThreeSplits (parent : Shape) : List Shape :=
  (shapes 4).filter fun child ↦ decide (child ≤ parent)

/-- The shared dyadic denominator of the archived certificate. -/
def dyadicDenominator : Nat := 2 ^ 32

/-- Exact arrays for the two positive-level-three probability families. -/
structure PositiveLevelThreeData where
  regionNumerators : Array (Array Nat)
  splitNumerators : Array (Array (Array Nat))

namespace PositiveLevelThreeData

/-- Number of positive level-three types: twenty-one shapes times six incoming regions. -/
def nodeCount : Nat := 126

/-- Number of decomposition regions. -/
def regionCount : Nat := 6

/-- Padded width of a level-three split row. -/
def splitSlotCount : Nat := 10

/-- The positive parent shape belonging to a node.  Six consecutive nodes share a shape. -/
def nodeShape (node : Fin nodeCount) : Shape :=
  (positiveShapes 8)[node.val / regionCount]?.getD default

/-- Whether a padded split slot represents a genuine split of the node's parent shape. -/
def splitSlotValid (node : Fin nodeCount) (slot : Fin splitSlotCount) : Prop :=
  slot.val < (levelThreeSplits (nodeShape node)).length

instance (node : Fin nodeCount) (slot : Fin splitSlotCount) :
    Decidable (splitSlotValid node slot) := by
  unfold splitSlotValid
  infer_instance

/-- Shape occupying a padded split slot.  Invalid slots receive the harmless default shape. -/
def splitShape (node : Fin nodeCount) (slot : Fin splitSlotCount) : Shape :=
  (levelThreeSplits (nodeShape node))[slot.val]?.getD default

end PositiveLevelThreeData

end AlgebraicComplexity.LevelFourReconstruction
