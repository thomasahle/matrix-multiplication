/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Leg

/-!
# Rational typed leaves: structural data

This is the dependency-minimal typed-leaf interface. It records an exact positive count table,
three visible coordinate maps, and three positive matrix dimensions. Finite products, probability,
entropy, and tensor semantics are supplied by separate adapters.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

/-- A strictly positive integral profile representing the rational law
`count i / sum_j count j`. Zero coordinates should be removed from the alphabet first. -/
structure PositiveIntegralProfile (I : Type u) where
  /-- Canonical finite alphabet used by all exact products. -/
  alphabet : Finset I
  /-- Every letter belongs to the canonical alphabet. -/
  complete : ∀ i, i ∈ alphabet
  count : I → ℕ
  count_pos : ∀ i, 0 < count i

namespace PositiveIntegralProfile

variable {I : Type u} [Fintype I]

/-- The stored canonical alphabet is extensionally the whole finite type. -/
theorem alphabet_eq_univ (profile : PositiveIntegralProfile I) :
    profile.alphabet = Finset.univ := by
  exact Finset.eq_univ_of_forall profile.complete

end PositiveIntegralProfile

/-- Paper-independent finite data carried by one rational typed leaf.

`coordinate` records the three interface labels. `dimension` records the corresponding positive
matrix dimensions for each support letter. -/
structure RationalTypedLeaf
    (I : Type u) (A : Leg → Type v) where
  profile : PositiveIntegralProfile I
  coordinate : ∀ c, I → A c
  dimension : I → Leg → ℕ
  dimension_pos : ∀ i c, 0 < dimension i c

end AlgebraicComplexity
