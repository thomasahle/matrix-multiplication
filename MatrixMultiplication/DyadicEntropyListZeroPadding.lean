/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropyListPermutation

/-!
# Zero-padding invariance of serialized dyadic entropy

The compact certificate bridge imports this module: it receives both permutation invariance and
the zero-padding law without adding either proof to the lightweight list-semantic core.
-/

namespace MatrixMultiplication.DyadicEntropyForm

open MatrixMultiplication.DyadicEntropy

noncomputable section

/-- Appending any finite amount of zero padding does not change homogeneous entropy. -/
@[simp] theorem weightedEntropyList_append_replicate_zero
    (bits : ℕ) (numerators : List ℕ) (padding : ℕ) :
    weightedEntropyList bits (numerators ++ List.replicate padding 0) =
      weightedEntropyList bits numerators := by
  simp [weightedEntropyList, entropyList, entropyTerm_zero]

end

end MatrixMultiplication.DyadicEntropyForm
