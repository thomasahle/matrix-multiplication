/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensor

/-!
# Lightweight total-weight alphabet for CW split words

This module contains only the finite total-weight alphabet and its map from complete-split words.
Keeping these definitions below the tensor-level quotient construction lets counting and
certificate clients avoid importing hashing, coarsening, and tensor restriction machinery.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

/-- A coarse digit is a possible total weight of one depth-`depth` complete-split chunk. -/
abbrev CWCoarseDigit (depth : ℕ) := Fin (2 ^ (depth + 1) + 1)

/-- Every complete-split word has weight at most the legal CW coarse total. -/
theorem splitWordWeight_le_coarseTotal (depth : ℕ) (word : SplitWord depth) :
    splitWordWeight word ≤ 2 ^ (depth + 1) := by
  unfold splitWordWeight
  calc
    (∑ position, (word position : ℕ)) ≤
        ∑ _position : Fin (2 ^ depth), 2 := by
      apply Finset.sum_le_sum
      intro position _
      omega
    _ = 2 ^ (depth + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Forget a complete-split word except for its total digit weight. -/
def cwSplitWordTotalDigit (depth : ℕ) (word : SplitWord depth) : CWCoarseDigit depth :=
  ⟨splitWordWeight word,
    Nat.lt_succ_iff.mpr (splitWordWeight_le_coarseTotal depth word)⟩

@[simp] theorem cwSplitWordTotalDigit_val (depth : ℕ) (word : SplitWord depth) :
    (cwSplitWordTotalDigit depth word : ℕ) = splitWordWeight word :=
  rfl

end AlgebraicComplexity.Examples
