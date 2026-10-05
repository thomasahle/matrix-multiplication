/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordCore
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

/-!
# Consecutive halves of complete-split words

This dependency-light module contains the canonical equivalence between a complete-split word and
its two consecutive half-words, together with literal concatenation.  It is the finite word-level
semantics behind complete split distributions in
`papers/sources/2404.16349/prelim.tex:249-269` of [alman2025more]; distributions, profiles, and
tensor realizations remain in downstream interface modules.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open scoped BigOperators

namespace AlgebraicComplexity

/-- Split the positions in a depth-`d+1` chunk into its two consecutive depth-`d` halves. -/
def splitIndexSuccEquiv (depth : ℕ) :
    Fin (2 ^ (depth + 1)) ≃ Fin (2 ^ depth) ⊕ Fin (2 ^ depth) :=
  (finCongr (by simp [pow_succ, Nat.mul_two])).trans finSumFinEquiv.symm

/-- A complete-split word at depth `d+1` is canonically a pair of depth-`d` words. -/
def splitWordSuccEquiv (depth : ℕ) :
    SplitWord (depth + 1) ≃ SplitWord depth × SplitWord depth :=
  (Equiv.arrowCongr (splitIndexSuccEquiv depth) (Equiv.refl SplitDigit)).trans
    (Equiv.sumArrowEquivProdArrow (Fin (2 ^ depth)) (Fin (2 ^ depth)) SplitDigit)

/-- The aggregate coordinate of a split word is the sum of the coordinates of its two halves. -/
theorem splitWordWeight_succ (depth : ℕ) (word : SplitWord (depth + 1)) :
    splitWordWeight word =
      splitWordWeight (splitWordSuccEquiv depth word).1 +
        splitWordWeight (splitWordSuccEquiv depth word).2 := by
  classical
  change (∑ i, (word i : ℕ)) = _
  calc
    (∑ i, (word i : ℕ)) =
        ∑ s, (word ((splitIndexSuccEquiv depth).symm s) : ℕ) := by
      simpa using
        (splitIndexSuccEquiv depth).sum_comp
          (fun s ↦ (word ((splitIndexSuccEquiv depth).symm s) : ℕ))
    _ = _ := by
      rw [Fintype.sum_sum_type]
      rfl

/-- Concatenate two child split words into their canonical parent word. -/
def concatSplitWords {depth : ℕ} (left right : SplitWord depth) :
    SplitWord (depth + 1) :=
  (splitWordSuccEquiv depth).symm (left, right)

/-- Splitting a concatenation returns the two words that were concatenated. -/
@[simp] theorem splitWordSuccEquiv_concatSplitWords {depth : ℕ}
    (left right : SplitWord depth) :
    splitWordSuccEquiv depth (concatSplitWords left right) = (left, right) :=
  (splitWordSuccEquiv depth).apply_symm_apply (left, right)

end AlgebraicComplexity
