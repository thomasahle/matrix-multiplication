/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Complete-split word alphabet

This dependency-light module defines ternary complete-split words and their aggregate digit sum.
Real distributions, empirical profiles, recursive divisions, and tensor realizations live in
downstream interface modules.
-/

open scoped BigOperators

namespace AlgebraicComplexity

/-- One base partition coordinate, represented by the values `0`, `1`, and `2`. -/
abbrev SplitDigit := Fin 3

/-- A complete-split chunk at zero-based recursion depth `depth`. -/
abbrev SplitWord (depth : ℕ) := Fin (2 ^ depth) → SplitDigit

/-- Sum of the ternary digits in one complete-split chunk. -/
def splitWordWeight {depth : ℕ} (word : SplitWord depth) : ℕ :=
  ∑ i, (word i : ℕ)

/-- Digitwise complementation `a ↦ 2-a` on a complete-split word. -/
def complementSplitWord {depth : ℕ} (word : SplitWord depth) : SplitWord depth :=
  fun position ↦ Fin.rev (word position)

@[simp] theorem complementSplitWord_apply {depth : ℕ} (word : SplitWord depth)
    (position : Fin (2 ^ depth)) :
    complementSplitWord word position = Fin.rev (word position) :=
  rfl

@[simp] theorem complementSplitWord_complementSplitWord {depth : ℕ}
    (word : SplitWord depth) :
    complementSplitWord (complementSplitWord word) = word := by
  funext position
  simp [complementSplitWord]

/-- A split word of weight zero is the all-zero word. -/
theorem splitWord_eq_zero_of_weight_eq_zero {depth : ℕ} (word : SplitWord depth)
    (hweight : splitWordWeight word = 0) :
    word = 0 := by
  funext position
  apply Fin.ext
  have hzero : ∀ p, (word p : ℕ) = 0 := by
    have hsum : (∑ p, (word p : ℕ)) = 0 := hweight
    exact fun p ↦ (Finset.sum_eq_zero_iff.mp hsum) p (Finset.mem_univ p)
  simpa using hzero position

end AlgebraicComplexity
