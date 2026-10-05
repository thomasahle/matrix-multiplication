/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MappedType

/-!
# Pushforwards after restricting an integral profile to its support

This file proves that zero-mass source letters can be removed before pushing an integral profile
forward with `WordType.mappedType`.  The main theorem allows any decidable source subtype outside
which the profile vanishes.  Its corollary specializes that statement to the canonical subtype of
letters carrying nonzero mass.

The result is purely finite combinatorics.  In particular, it lets certificate clients replace a
padded ambient index type by the subtype of active rows without changing any pushed marginal.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

/-- Restricting the source alphabet to any subtype containing the support of an integral profile
does not change its pushforward.

Proof sketch: evaluate both pushforwards at an arbitrary target letter.  The restricted sum is the
ambient sum over the chosen subtype.  Every omitted ambient summand is zero because its profile
weight is zero, so the two fiber sums agree. -/
theorem mappedType_subtype_eq_of_eq_zero_outside
    {A B : Type*} [Fintype A] {P : A → Prop} [DecidablePred P]
    (f : A → B) (profile : A → ℕ)
    (hzero : ∀ a, ¬ P a → profile a = 0) :
    mappedType (fun a : Subtype P ↦ f a.1) (fun a : Subtype P ↦ profile a.1) =
      mappedType f profile := by
  classical
  funext b
  rw [mappedType_eq_sum_ite, mappedType_eq_sum_ite]
  calc
    (∑ a : Subtype P, if f a.1 = b then profile a.1 else 0) =
        ∑ a ∈ Finset.univ.filter P, if f a = b then profile a else 0 := by
      exact (Finset.sum_subtype (Finset.univ.filter P) (fun _ ↦ by simp)
        (fun a ↦ if f a = b then profile a else 0)).symm
    _ = ∑ a : A, if f a = b then profile a else 0 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      have hnot : ¬ P a := by
        simpa using ha
      simp [hzero a hnot]

/-- Restricting an integral profile to its nonzero-support subtype does not change its
pushforward.

Proof sketch: apply `mappedType_subtype_eq_of_eq_zero_outside`.  Outside the displayed subtype,
the statement that the profile is not nonzero is exactly the statement that it is zero. -/
theorem mappedType_activeSupport
    {A B : Type*} [Fintype A] (f : A → B) (profile : A → ℕ) :
    mappedType (fun a : {a // profile a ≠ 0} ↦ f a.1)
        (fun a : {a // profile a ≠ 0} ↦ profile a.1) =
      mappedType f profile := by
  apply mappedType_subtype_eq_of_eq_zero_outside
  intro a ha
  simpa using ha

end AlgebraicComplexity.WordType
