/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildOccurrences

set_option autoImplicit false

/-!
# Empirical profiles of labelled recursive children

This file adds the method-of-types statement to the dependency-light labelled-child word API.
It is split from `RecursiveChildOccurrences` because the full `WordType` theorem layer has a much
larger elaboration footprint than the finite half-word semantics.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

/-- Applying the same observation to all labelled children commutes with the left/right append. -/
theorem map_positiveWordLabelledChildren_eq_append
    {A : Type u} {B : Type v} {depth n : ℕ}
    (encode : A → RecursiveSplitWord (depth + 1))
    (observe : RecursiveSplitWord depth → B)
    (word : PositiveWord A n) :
    observe ∘ positiveWordLabelledChildren encode word =
      Fin.append (observe ∘ positiveWordLeftChildren encode word)
        (observe ∘ positiveWordRightChildren encode word) := by
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence
  · intro sample
    simp only [Function.comp_apply, positiveWordLabelledChildren_left,
      Fin.append_left, positiveWordLeftChildren]
  · intro sample
    rw [Function.comp_apply, positiveWordLabelledChildren_right,
      Fin.append_right, Function.comp_apply]
    rfl

/-- The empirical profile of an observed labelled-child word is exactly the sum of its left and
right empirical profiles.  No set quotient is taken, so a self-complementary child contributes
once in each summand. -/
theorem multiplicity_map_positiveWordLabelledChildren
    {A : Type u} {B : Type v} [Fintype B] {depth n : ℕ}
    (encode : A → RecursiveSplitWord (depth + 1))
    (observe : RecursiveSplitWord depth → B)
    (word : PositiveWord A n) :
    WordType.multiplicity (observe ∘ positiveWordLabelledChildren encode word) =
      WordType.multiplicity (observe ∘ positiveWordLeftChildren encode word) +
        WordType.multiplicity (observe ∘ positiveWordRightChildren encode word) := by
  rw [map_positiveWordLabelledChildren_eq_append, WordType.multiplicity_append]

end AlgebraicComplexity
