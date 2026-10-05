/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralProfileCounts
import AlgebraicComplexity.Combinatorics.WordType

/-! # Finite proportional type classes -/

namespace AlgebraicComplexity.WordType

universe u

variable {I : Type u} [Fintype I]

/-- Pushing a scaled integral profile is the same as scaling its pushforward. -/
theorem mappedType_proportionalCounts
    {A B : Type*} [Fintype A] (f : A → B) (profile : A → ℕ) (k : ℕ) :
    mappedType f (proportionalCounts profile k) =
      proportionalCounts (mappedType f profile) k := by
  classical
  funext b
  simp only [mappedType, proportionalCounts, Finset.sum_mul]

/-- Proportional counts always form a valid type of the proportionally scaled word length. -/
theorem proportionalCounts_mem_types (profile : I → ℕ) (k : ℕ) :
    proportionalCounts profile k ∈ types I (profileMass profile * k) := by
  rw [mem_types]
  simp only [profileMass, proportionalCounts, Finset.sum_mul]

/-- Every proportional type class is nonempty, including zero mass and zero repetition. -/
theorem card_proportionalTypeClass_pos (profile : I → ℕ) (k : ℕ) :
    0 < (typeClass (profileMass profile * k)
      (proportionalCounts profile k)).card := by
  rw [Finset.card_pos]
  exact typeClass_nonempty _ (proportionalCounts_mem_types profile k)

end AlgebraicComplexity.WordType
