/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MappedType

/-!
# Elementary identities for pushforwards of integral profiles

Layer 3 (`AlgebraicComplexity/Combinatorics/`).  `Combinatorics/MappedType.lean` introduces
`WordType.mappedType` together with the two facts a client normally needs first --- that it is a
sum over letter fibers (`mappedType_eq_sum_ite`) and that it preserves total mass
(`profileMass_mappedType`).  This module adds the remaining elementary identities.  All of them
live in that same tiny cone: no words, no multinomial coefficients, no entropy.

## Principal results

* `mappedType_id` and `mappedType_congr` --- the two companions of functoriality.  Functoriality
  itself, `WordType.mappedType_comp`, is **committed already** in
  `Combinatorics/WordType.lean`; it is deliberately *not* restated here.
* `exists_of_mappedType_ne_zero` --- the support of a pushed-forward profile lies in the image of
  the map.  This is the fact a counting client uses to see that a word carrying a prescribed
  pushed-forward type only ever spells letters that some source letter maps onto, which is how a
  type class over a large ambient alphabet is confined to a small support.

## Position in the library

The cone is `Combinatorics/MappedType.lean` and hence `Combinatorics/IntegralProfileCounts.lean`;
nothing else.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

/-- **The identity pushforward is the identity.**  The letter fiber of `id` over `b` is the
singleton `{b}`. -/
theorem mappedType_id {A : Type*} [Fintype A] (a : A → ℕ) :
    mappedType (id : A → A) a = a := by
  classical
  funext b
  have hfiber : letterFiber (id : A → A) b = {b} := by
    ext x
    simp [mem_letterFiber]
  show ∑ x ∈ letterFiber (id : A → A) b, a x = a b
  rw [hfiber, Finset.sum_singleton]

/-- **A pushforward depends on its map only pointwise.**  Convenient when a composite of two
readings is only propositionally, not definitionally, the reading a committed marginal identity is
stated at. -/
theorem mappedType_congr {A B : Type*} [Fintype A] {f g : A → B} (h : ∀ x, f x = g x)
    (a : A → ℕ) : mappedType f a = mappedType g a := by
  have hfg : f = g := funext h
  rw [hfg]

/-- **The support of a pushforward lies in the image of the map.**  If the pushed-forward profile
charges a target letter then some source letter lying over it is itself charged. -/
theorem exists_of_mappedType_ne_zero {A B : Type*} [Fintype A] {f : A → B} {a : A → ℕ} {b : B}
    (h : mappedType f a b ≠ 0) : ∃ x, f x = b ∧ a x ≠ 0 := by
  classical
  by_contra hcon
  refine h ?_
  show ∑ x ∈ letterFiber f b, a x = 0
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  by_contra hax
  exact hcon ⟨x, mem_letterFiber.mp hx, hax⟩

end AlgebraicComplexity.WordType
