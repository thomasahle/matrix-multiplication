/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourShapeGeometry
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildShape
import AlgebraicComplexity.Tensor.Basic

set_option autoImplicit false

/-!
# Bridge from executable shape triples to recursive child alphabets

Certificate evaluators naturally store a constituent shape as a three-field structure, while the
tensor-facing recursive API indexes coordinates by `Leg`.  This file supplies the lossless bridge
between those representations, including arbitrary coordinate orientations and complementation.
It contains no certificate arrays or tensor extraction theorem.
-/

namespace AlgebraicComplexity
namespace LevelFourReconstruction

open Tensor

namespace Shape

/-- Read an executable shape by tensor leg. -/
def leg (shape : Shape) : Leg → ℕ
  | .X => shape.x
  | .Y => shape.y
  | .Z => shape.z

@[simp] theorem leg_X (shape : Shape) : shape.leg .X = shape.x := rfl
@[simp] theorem leg_Y (shape : Shape) : shape.leg .Y = shape.y := rfl
@[simp] theorem leg_Z (shape : Shape) : shape.leg .Z = shape.z := rfl

/-- Read physical coordinates in an arbitrary logical orientation. -/
def orientedLeg (shape : Shape) (sigma : Orientation) : Leg → ℕ :=
  fun c ↦ shape.leg (sigma c)

@[simp] theorem orientedLeg_apply (shape : Shape) (sigma : Orientation) (c : Leg) :
    shape.orientedLeg sigma c = shape.leg (sigma c) :=
  rfl

/-- Reordering the three legs preserves the coordinate total. -/
theorem orientedLeg_total (shape : Shape) (sigma : Orientation) :
    shape.orientedLeg sigma .X + shape.orientedLeg sigma .Y +
        shape.orientedLeg sigma .Z = shape.total := by
  have hperm : (∑ c : Leg, shape.leg (sigma c)) = ∑ c : Leg, shape.leg c :=
    Equiv.sum_comp sigma shape.leg
  calc
    shape.orientedLeg sigma .X + shape.orientedLeg sigma .Y +
        shape.orientedLeg sigma .Z = ∑ c : Leg, shape.leg (sigma c) := by
          simp [orientedLeg, Tensor.sum_leg]
    _ = ∑ c : Leg, shape.leg c := hperm
    _ = shape.total := by simp [Tensor.sum_leg, Shape.total]

/-- Coordinatewise containment is preserved when parent and child use the same orientation. -/
theorem orientedLeg_le {child parent : Shape} (h : child ≤ parent)
    (sigma : Orientation) (c : Leg) :
    child.orientedLeg sigma c ≤ parent.orientedLeg sigma c := by
  cases hs : sigma c with
  | X => simpa [orientedLeg, leg, hs] using h.1
  | Y => simpa [orientedLeg, leg, hs] using h.2.1
  | Z => simpa [orientedLeg, leg, hs] using h.2.2

/-- Truncated coordinatewise complementation always remains inside the parent box. -/
theorem complement_le (parent child : Shape) : parent.complement child ≤ parent := by
  exact ⟨Nat.sub_le _ _, Nat.sub_le _ _, Nat.sub_le _ _⟩

/-- Convert a contained fixed-total executable shape to the finite recursive-child alphabet. -/
def toRecursiveChildShape {child parent : Shape} {childTotal : ℕ}
    (sigma : Orientation) (hchild : child.total = childTotal) (hle : child ≤ parent) :
    RecursiveChildShape (parent.orientedLeg sigma) childTotal :=
  RecursiveChildShape.ofCoordinates (child.orientedLeg sigma)
    (child.orientedLeg_le hle sigma) (by rw [child.orientedLeg_total, hchild])

@[simp] theorem get_toRecursiveChildShape {child parent : Shape} {childTotal : ℕ}
    (sigma : Orientation) (hchild : child.total = childTotal) (hle : child ≤ parent)
    (c : Leg) :
    (toRecursiveChildShape sigma hchild hle).get c = child.orientedLeg sigma c :=
  RecursiveChildShape.get_ofCoordinates _ _ _ c

/-- Executable shape complementation agrees with the recursive alphabet's involution. -/
theorem toRecursiveChildShape_complement
    {child parent : Shape} {childTotal : ℕ}
    (sigma : Orientation)
    (hparent : parent.total = 2 * childTotal)
    (hchild : child.total = childTotal) (hle : child ≤ parent) :
    toRecursiveChildShape sigma
        (by rw [Shape.complement_total_of_le hle, hparent, hchild]; omega)
        (parent.complement_le child) =
      RecursiveChildShape.complement
        (by rw [parent.orientedLeg_total, hparent])
        (toRecursiveChildShape sigma hchild hle) := by
  apply RecursiveChildShape.ext
  intro c
  simp only [get_toRecursiveChildShape, RecursiveChildShape.complement_get]
  cases hs : sigma c <;> simp [orientedLeg, leg, Shape.complement, hs]

end Shape
end LevelFourReconstruction
end AlgebraicComplexity
