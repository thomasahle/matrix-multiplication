/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Leg
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Definition-only three-legged tensor core

This file contains the smallest public representation layer needed to state constructive tensor
rank and concrete matrix-multiplication tensors: the `Tensor3` abbreviation, named-leg families,
pure tensors, and the one scalar rule used by the existence proof for finite rank certificates.

The established `Tensor/Basic.lean` import re-exports these declarations and adds the broader
pure-tensor, map, and permutation calculus.  Keeping the definitions here prevents lightweight
rank and matrix-tensor statements from loading that theorem olean or coordinate-basis machinery.
-/

namespace AlgebraicComplexity.Tensor

universe u v

/-- A trilinear tensor whose ambient space on leg `i` is `V i`. -/
abbrev Tensor3 (K : Type u) [CommSemiring K] (V : Leg → Type v)
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)] :=
  PiTensorProduct K V

/-- Assemble a dependent family by giving its `X`, `Y`, and `Z` components. -/
def ofLegs {V : Leg → Type v} (x : V .X) (y : V .Y) (z : V .Z) : ∀ i, V i
  | .X => x
  | .Y => y
  | .Z => z

/-- Evaluating the assembled family `ofLegs x y z` at leg `X` returns `x`. -/
@[simp] theorem ofLegs_X {V : Leg → Type v} (x : V .X) (y : V .Y) (z : V .Z) :
    ofLegs x y z .X = x := rfl

/-- Evaluating the assembled family `ofLegs x y z` at leg `Y` returns `y`. -/
@[simp] theorem ofLegs_Y {V : Leg → Type v} (x : V .X) (y : V .Y) (z : V .Z) :
    ofLegs x y z .Y = y := rfl

/-- Evaluating the assembled family `ofLegs x y z` at leg `Z` returns `z`. -/
@[simp] theorem ofLegs_Z {V : Leg → Type v} (x : V .X) (y : V .Y) (z : V .Z) :
    ofLegs x y z .Z = z := rfl

/-- Eta rule: reassembling a dependent family from its three leg components gives back the
original family. -/
@[simp] theorem ofLegs_eta {V : Leg → Type v} (f : ∀ i, V i) :
    ofLegs (f .X) (f .Y) (f .Z) = f := by
  funext c
  cases c <;> rfl

/-- Overwriting the `X` component of `ofLegs x₀ y z` with `x` yields `ofLegs x y z`. -/
@[simp] theorem update_ofLegs_X {V : Leg → Type v}
    (x₀ x : V .X) (y : V .Y) (z : V .Z) :
    Function.update (ofLegs x₀ y z) .X x = ofLegs x y z := by
  funext c
  cases c <;> rfl

section

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]

/-- A pure three-legged tensor. -/
abbrev pure (x : ∀ i, V i) : Tensor3 K V :=
  PiTensorProduct.tprod K x

/-- A scalar factor on the `X` component of a pure tensor pulls out as a scalar multiple of the
whole tensor. -/
@[simp] theorem pure_ofLegs_smul_X (a : K) (x : V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs (a • x) y z) = a • pure (K := K) (ofLegs x y z) := by
  simpa only [update_ofLegs_X] using
    (PiTensorProduct.tprod K).map_update_smul (ofLegs (0 : V .X) y z) .X a x

end

end AlgebraicComplexity.Tensor
