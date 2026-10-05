/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Leg
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false

/-!
# Finite ordered child-shape alphabets

For a parent constituent shape `s`, the recursive split variable ranges over triples `u`
contained coordinatewise in `s` and having the prescribed child total.  This module packages
that finite alphabet and its involution `u ↦ s - u`.  Using a subtype of three bounded `Fin`
coordinates makes finiteness structural and avoids treating truncated subtraction as a
permutation of all natural triples.
-/

namespace AlgebraicComplexity

open Tensor

/-- A coordinatewise-bounded three-coordinate tuple. -/
abbrev BoundedShape (parent : Leg → ℕ) :=
  Fin (parent .X + 1) × Fin (parent .Y + 1) × Fin (parent .Z + 1)

/-- Ordered child shapes of a fixed total inside a fixed parent shape. -/
abbrev RecursiveChildShape (parent : Leg → ℕ) (childTotal : ℕ) :=
  {u : BoundedShape parent //
    (u.1 : ℕ) + (u.2.1 : ℕ) + (u.2.2 : ℕ) = childTotal}

namespace RecursiveChildShape

variable {parent : Leg → ℕ} {childTotal : ℕ}

/-- Read one coordinate of a bounded child shape. -/
def get (u : RecursiveChildShape parent childTotal) : Leg → ℕ
  | .X => u.1.1
  | .Y => u.1.2.1
  | .Z => u.1.2.2

@[simp] theorem get_X (u : RecursiveChildShape parent childTotal) :
    u.get .X = u.1.1 :=
  rfl

@[simp] theorem get_Y (u : RecursiveChildShape parent childTotal) :
    u.get .Y = u.1.2.1 :=
  rfl

@[simp] theorem get_Z (u : RecursiveChildShape parent childTotal) :
    u.get .Z = u.1.2.2 :=
  rfl

/-- Every child coordinate is bounded by its parent coordinate. -/
theorem get_le_parent (u : RecursiveChildShape parent childTotal) (c : Leg) :
    u.get c ≤ parent c := by
  cases c with
  | X => exact Nat.le_of_lt_succ u.1.1.isLt
  | Y => exact Nat.le_of_lt_succ u.1.2.1.isLt
  | Z => exact Nat.le_of_lt_succ u.1.2.2.isLt

/-- The three coordinates of a child shape have the prescribed total. -/
theorem total_eq (u : RecursiveChildShape parent childTotal) :
    u.get .X + u.get .Y + u.get .Z = childTotal :=
  u.2

/-- Build a bounded child shape from an arbitrary leg-indexed coordinate function. -/
def ofCoordinates (coordinates : Leg → ℕ)
    (hle : ∀ c, coordinates c ≤ parent c)
    (htotal : coordinates .X + coordinates .Y + coordinates .Z = childTotal) :
    RecursiveChildShape parent childTotal :=
  ⟨((⟨coordinates .X, Nat.lt_succ_iff.mpr (hle .X)⟩ : Fin (parent .X + 1)),
      ((⟨coordinates .Y, Nat.lt_succ_iff.mpr (hle .Y)⟩ : Fin (parent .Y + 1)),
        (⟨coordinates .Z, Nat.lt_succ_iff.mpr (hle .Z)⟩ : Fin (parent .Z + 1)))),
    htotal⟩

@[simp] theorem get_ofCoordinates (coordinates : Leg → ℕ)
    (hle : ∀ c, coordinates c ≤ parent c)
    (htotal : coordinates .X + coordinates .Y + coordinates .Z = childTotal)
    (c : Leg) :
    (ofCoordinates coordinates hle htotal).get c = coordinates c := by
  cases c <;> rfl

/-- Child shapes are determined by their three leg coordinates. -/
@[ext] theorem ext {left right : RecursiveChildShape parent childTotal}
    (h : ∀ c, left.get c = right.get c) : left = right := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact h .X
  · apply Prod.ext
    · apply Fin.ext
      exact h .Y
    · apply Fin.ext
      exact h .Z

/-- Coordinatewise complement inside the parent bounds.  The parent-total hypothesis makes the
complement have the same child total. -/
def complement
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (u : RecursiveChildShape parent childTotal) :
    RecursiveChildShape parent childTotal :=
  ofCoordinates (fun c ↦ parent c - u.get c) (fun c ↦ Nat.sub_le _ _) (by
    have hx := u.get_le_parent .X
    have hy := u.get_le_parent .Y
    have hz := u.get_le_parent .Z
    have hu := u.total_eq
    omega)

@[simp] theorem complement_get
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (u : RecursiveChildShape parent childTotal) (c : Leg) :
    (u.complement hparent).get c = parent c - u.get c := by
  apply get_ofCoordinates

/-- Complementation is involutive on the bounded child alphabet. -/
theorem complement_complement
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (u : RecursiveChildShape parent childTotal) :
    (u.complement hparent).complement hparent = u := by
  apply ext
  intro c
  simp [Nat.sub_sub_self (u.get_le_parent c)]

/-- The coordinatewise complement as a self-inverse permutation. -/
def complementPerm
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal) :
    Equiv.Perm (RecursiveChildShape parent childTotal) where
  toFun := complement hparent
  invFun := complement hparent
  left_inv := complement_complement hparent
  right_inv := complement_complement hparent

@[simp] theorem complementPerm_apply
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (u : RecursiveChildShape parent childTotal) :
    complementPerm hparent u = u.complement hparent :=
  rfl

@[simp] theorem complementPerm_symm
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal) :
    (complementPerm hparent).symm = complementPerm hparent :=
  rfl

/-- A child coordinate and its complement add to the parent coordinate. -/
theorem get_add_complement_get
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (u : RecursiveChildShape parent childTotal) (c : Leg) :
    u.get c + (complementPerm hparent u).get c = parent c := by
  rw [complementPerm_apply, complement_get]
  exact Nat.add_sub_of_le (u.get_le_parent c)

end RecursiveChildShape
end AlgebraicComplexity
