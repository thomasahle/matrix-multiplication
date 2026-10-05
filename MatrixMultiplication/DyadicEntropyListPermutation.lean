/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropyList

/-!
# Permutation invariance of serialized dyadic entropy

This proof is isolated from the list-semantic core so downstream numerical clients do not pay
for it unless they compare two serialization orders.
-/

namespace MatrixMultiplication.DyadicEntropyForm

open MatrixMultiplication.DyadicEntropy

noncomputable section

/-- Permuting a serialized numerator row does not change its homogeneous entropy. -/
theorem weightedEntropyList_eq_of_perm
    {bits : ℕ} {left right : List ℕ} (hperm : left.Perm right) :
    weightedEntropyList bits left = weightedEntropyList bits right := by
  unfold weightedEntropyList entropyList
  rw [(hperm.map (entropyTerm bits)).sum_eq, hperm.sum_eq]

end

end MatrixMultiplication.DyadicEntropyForm
