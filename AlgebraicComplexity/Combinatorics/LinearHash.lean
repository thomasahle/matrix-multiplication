/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite linear hashes

This module contains the paper-independent algebra behind universal linear hashing over a finite
field.  A nonzero dot-product functional is surjective, all of its fibers are translates of its
kernel, and consequently every fiber occupies exactly a `1 / |R|` fraction of the weight space.

The results are stated first as exact finite-cardinality identities.  Probability libraries can
then turn them into distributional or conditional-probability statements without introducing a
second counting argument.

The plain algebra of the dot product needs only a commutative ring, so it is stated there; the
surjectivity, fiber, and cardinality results genuinely use inversion and are stated over a field.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace FiniteLinearHash

variable {ι : Type v} [Fintype ι]

section CommRing

variable {R : Type u} [CommRing R]

/-- Dot product of a freely chosen weight table with a fixed coefficient table. -/
def dot (weights coefficients : ι → R) : R :=
  ∑ i, weights i * coefficients i

/-- The dot product, viewed as an additive homomorphism in its weight argument. -/
def dotAddHom (coefficients : ι → R) : (ι → R) →+ R where
  toFun weights := dot weights coefficients
  map_zero' := by simp [dot]
  map_add' left right := by
    simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp] theorem dotAddHom_apply (coefficients weights : ι → R) :
    dotAddHom coefficients weights = dot weights coefficients :=
  rfl

/-- Subtraction in the coefficient table becomes subtraction of hash values. -/
theorem dot_sub (weights left right : ι → R) :
    dot weights (left - right) = dot weights left - dot weights right := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

/-- Equality of two dot products is the zero fiber for their coefficient difference. -/
theorem dot_sub_eq_zero_iff (weights left right : ι → R) :
    dot weights (left - right) = 0 ↔ dot weights left = dot weights right := by
  rw [dot_sub, sub_eq_zero]

end CommRing

section Field

variable {R : Type u} [Field R]

/-- A nonzero coefficient table makes the dot-product hash surjective. -/
theorem dotAddHom_surjective {coefficients : ι → R} (hcoefficients : coefficients ≠ 0) :
    Function.Surjective (dotAddHom coefficients) := by
  classical
  have hpivot : ∃ pivot, coefficients pivot ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hcoefficients
    funext i
    exact h i
  obtain ⟨pivot, hpivot⟩ := hpivot
  intro target
  let weights : ι → R := Function.update 0 pivot (target / coefficients pivot)
  refine ⟨weights, ?_⟩
  rw [dotAddHom_apply, dot, Finset.sum_eq_single pivot]
  · simp [weights, hpivot]
  · intro i _ hi
    simp [weights, hi]
  · simp

/-- Every fiber of a nonzero dot-product hash is equivalent to its kernel. -/
noncomputable def dotFiberEquivKer {coefficients : ι → R} (hcoefficients : coefficients ≠ 0)
    (target : R) :
    {weights : ι → R // dot weights coefficients = target} ≃ (dotAddHom coefficients).ker :=
  (Equiv.refl _).trans
    (AddMonoidHom.fiberEquivKerOfSurjective (dotAddHom_surjective hcoefficients) target)

/-- Exact cardinality form of the `1 / |R|` law: the size of any fiber, multiplied by the field
size, is the size of the complete weight space. -/
theorem card_dot_fiber_mul {coefficients : ι → R} (hcoefficients : coefficients ≠ 0)
    (target : R) :
    Nat.card {weights : ι → R // dot weights coefficients = target} * Nat.card R =
      Nat.card (ι → R) := by
  let f := dotAddHom coefficients
  have hsurjective : Function.Surjective f := dotAddHom_surjective hcoefficients
  calc
    Nat.card {weights : ι → R // dot weights coefficients = target} * Nat.card R =
        Nat.card f.ker * Nat.card R := by
          rw [Nat.card_congr (dotFiberEquivKer hcoefficients target)]
    _ = Nat.card f.ker * f.ker.index := by
      congr 1
      rw [AddSubgroup.index_ker]
      rw [AddMonoidHom.range_eq_top.mpr hsurjective]
      exact Nat.card_congr (Equiv.Set.univ R).symm
    _ = Nat.card (ι → R) := f.ker.card_mul_index

end Field

end FiniteLinearHash

end AlgebraicComplexity
