/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType

/-!
# Additive statistics of finite word types

A multiplicity type determines every statistic obtained by summing a fixed letter weight over
the positions of a word.  This is the additive counterpart of
`WordType.prod_word_eq_prod_pow`, and is useful whenever an exact type must determine a product
dimension through its prime exponents.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι]

/-- An additive statistic of a finite word is the multiplicity-weighted statistic of its
alphabet. -/
theorem sum_word_eq_sum_multiplicity_mul
    (statistic : ι → ℕ) (word : Fin n → ι) :
    ∑ position, statistic (word position) =
      ∑ letter, multiplicity word letter * statistic letter := by
  classical
  rw [← Finset.sum_fiberwise'
    (s := (Finset.univ : Finset (Fin n))) word statistic]
  apply Finset.sum_congr rfl
  intro letter _
  simp [multiplicity]

/-- Words with the same multiplicity type have the same value for every additive statistic. -/
theorem sum_word_eq_of_multiplicity_eq
    (statistic : ι → ℕ) {left right : Fin n → ι}
    (h : multiplicity left = multiplicity right) :
    ∑ position, statistic (left position) =
      ∑ position, statistic (right position) := by
  rw [sum_word_eq_sum_multiplicity_mul, sum_word_eq_sum_multiplicity_mul, h]

end AlgebraicComplexity.WordType
