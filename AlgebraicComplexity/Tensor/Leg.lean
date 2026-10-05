/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Insert

/-!
# The three tensor legs

This lightweight module contains only the finite index type and its permutations.  Semantic
clients that manipulate three coordinate rates or dimensions can import it without loading the
finite-dimensional tensor-product implementation.
-/

namespace AlgebraicComplexity.Tensor

/-- The three legs of a trilinear tensor. -/
inductive Leg
  | X | Y | Z
  deriving DecidableEq, Repr

/-- The three legs `X`, `Y`, `Z` form a finite type. -/
instance : Fintype Leg where
  elems := {Leg.X, Leg.Y, Leg.Z}
  complete x := by cases x <;> simp

/-- A permutation of the three tensor legs. -/
abbrev Orientation := Equiv.Perm Leg

/-- The orientation `(X,Z,Y)`. -/
def xzy : Orientation where
  toFun
    | .X => .X
    | .Y => .Z
    | .Z => .Y
  invFun
    | .X => .X
    | .Y => .Z
    | .Z => .Y
  left_inv c := by cases c <;> rfl
  right_inv c := by cases c <;> rfl

/-- The cyclic orientation `X ↦ Y ↦ Z ↦ X`. -/
def cycle : Orientation where
  toFun
    | .X => .Y
    | .Y => .Z
    | .Z => .X
  invFun
    | .X => .Z
    | .Y => .X
    | .Z => .Y
  left_inv c := by cases c <;> rfl
  right_inv c := by cases c <;> rfl

@[simp] theorem xzy_X : xzy Leg.X = Leg.X := rfl
@[simp] theorem xzy_Y : xzy Leg.Y = Leg.Z := rfl
@[simp] theorem xzy_Z : xzy Leg.Z = Leg.Y := rfl
@[simp] theorem xzy_symm_X : xzy.symm Leg.X = Leg.X := rfl
@[simp] theorem xzy_symm_Y : xzy.symm Leg.Y = Leg.Z := rfl
@[simp] theorem xzy_symm_Z : xzy.symm Leg.Z = Leg.Y := rfl

@[simp] theorem cycle_X : cycle Leg.X = Leg.Y := rfl
@[simp] theorem cycle_Y : cycle Leg.Y = Leg.Z := rfl
@[simp] theorem cycle_Z : cycle Leg.Z = Leg.X := rfl
@[simp] theorem cycle_symm_X : cycle.symm Leg.X = Leg.Z := rfl
@[simp] theorem cycle_symm_Y : cycle.symm Leg.Y = Leg.X := rfl
@[simp] theorem cycle_symm_Z : cycle.symm Leg.Z = Leg.Y := rfl

end AlgebraicComplexity.Tensor
