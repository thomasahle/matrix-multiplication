/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

/-!
# Holes in a heterogeneous finite product

The complement of a coordinatewise-present product inside a coordinatewise-ambient product is
covered by the union of the cylinders in which one coordinate is missing.  Taking cardinalities
gives the usual union bound, with the other coordinates allowed to range over their full ambient
sets.

The result does not need the present coordinate sets to be contained in the ambient coordinate
sets: membership in the ambient product supplies the required ambient membership at the missing
coordinate.

## Reference and scope

This is the elementary finite cylinder-union calculation needed to transport input-hole budgets
through heterogeneous products. Its application is motivated by [alman2025more], *More Asymmetry
Yields Faster Matrix Multiplication*,
`papers/sources/2404.16349/constituent.tex:173-177,338-348,473-497`; that paper states the
constituent hole estimates, not this separately named product lemma.
For the three cyclic factors of the Total-Weight construction it adds the three relative
hole budgets. It neither establishes any of those budgets nor identifies a damaged tensor
with its intended child; those are separate constituent-theorem obligations.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v

/-- A heterogeneous product loses at most the sum of its one-coordinate hole cylinders.

The product indexed by `{j // j ≠ i}` is the ambient volume in all coordinates other than the
chosen missing coordinate `i`.  This formulation remains valid when an ambient coordinate is
empty and uses no division or positivity premise. -/
theorem card_piFinset_sdiff_piFinset_le_sum
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {α : ι → Type v} [∀ i, DecidableEq (α i)]
    (ambient present : ∀ i, Finset (α i)) :
    (Fintype.piFinset ambient \ Fintype.piFinset present).card ≤
      ∑ i : ι, (ambient i \ present i).card *
        ∏ j : {j : ι // j ≠ i}, (ambient j.1).card := by
  classical
  let badAt : ι → Finset (∀ i, α i) := fun i =>
    Fintype.piFinset
      (Function.update ambient i (ambient i \ present i))
  have hcover :
      Fintype.piFinset ambient \ Fintype.piFinset present ⊆
        Finset.univ.biUnion badAt := by
    intro x hx
    obtain ⟨hxAmbient, hxPresent⟩ := Finset.mem_sdiff.mp hx
    have hmissing : ∃ i, x i ∉ present i := by
      by_contra hnone
      apply hxPresent
      refine Fintype.mem_piFinset.mpr fun i => ?_
      by_contra hi
      exact hnone ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmissing
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
    change x ∈ Fintype.piFinset
      (Function.update ambient i (ambient i \ present i))
    refine Fintype.mem_piFinset.mpr fun j => ?_
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self, Finset.mem_sdiff]
      exact ⟨Fintype.mem_piFinset.mp hxAmbient i, hi⟩
    · simpa [hji] using Fintype.mem_piFinset.mp hxAmbient j
  have hbadCard (i : ι) :
      (badAt i).card =
        (ambient i \ present i).card *
          ∏ j : {j : ι // j ≠ i}, (ambient j.1).card := by
    change (Fintype.piFinset
      (Function.update ambient i (ambient i \ present i))).card = _
    rw [Fintype.card_piFinset,
      Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [j.property]
  calc
    (Fintype.piFinset ambient \ Fintype.piFinset present).card ≤
        (Finset.univ.biUnion badAt).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ i : ι, (badAt i).card := Finset.card_biUnion_le
    _ = ∑ i : ι, (ambient i \ present i).card *
        ∏ j : {j : ι // j ≠ i}, (ambient j.1).card := by
      exact Finset.sum_congr rfl fun i _ => hbadCard i

end AlgebraicComplexity
