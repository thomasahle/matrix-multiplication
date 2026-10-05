/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import AlgebraicComplexity.Combinatorics.IntegralProfileCounts

/-!
# Pushforwards of finite integral profiles

These definitions are the lightweight common interface between exact rational profiles and the
full method-of-types development.  They do not require words, multinomial coefficients, or
multivariate polynomials.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

/-- Letters lying over one value of a finite alphabet map. -/
noncomputable def letterFiber {A B : Type*} [Fintype A]
    (f : A → B) (b : B) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ f a = b

@[simp] theorem mem_letterFiber {A B : Type*} [Fintype A]
    {f : A → B} {a : A} {b : B} :
    a ∈ letterFiber f b ↔ f a = b := by
  classical
  simp [letterFiber]

/-- Push a multiplicity profile forward along a map of finite alphabets. -/
noncomputable def mappedType {A B : Type*} [Fintype A]
    (f : A → B) (a : A → ℕ) : B → ℕ :=
  fun b ↦ ∑ x ∈ letterFiber f b, a x

/-- A pushed-forward multiplicity profile as a sum of indicators. -/
theorem mappedType_eq_sum_ite {A : Type*} [Fintype A] {B : Type*} [DecidableEq B]
    (f : A → B) (a : A → ℕ) (b : B) :
    mappedType f a b = ∑ x, if f x = b then a x else 0 := by
  classical
  rw [← Finset.sum_filter]
  show ∑ x ∈ letterFiber f b, a x = _
  congr 1
  ext x
  simp

/-- A finite pushforward preserves the total mass of an integral profile. -/
theorem profileMass_mappedType {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (profile : A → ℕ) :
    profileMass (mappedType f profile) = profileMass profile := by
  classical
  unfold profileMass mappedType letterFiber
  exact Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset B))
    (fun a _ha ↦ Finset.mem_univ (f a)) profile

end AlgebraicComplexity.WordType
