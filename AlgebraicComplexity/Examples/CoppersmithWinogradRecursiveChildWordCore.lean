/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordCore
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightCore
import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetCore
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildOccurrences
import AlgebraicComplexity.Tensor.PartitionedCore

set_option autoImplicit false

/-!
# Recursive Coppersmith--Winograd labelled-child words

This dependency-light module exposes the exact finite word seen by the recursive compatibility
conditions.  Each parent occurrence contributes its labelled left child and its labelled right
child, in that order.  This is the finite address underlying the complete-split compatibility
cells of [alman2025more], Claim 6.18
(`papers/sources/2404.16349/constituent.tex:404-429`).  Tensor coarsening, hashing, and counting
remain in downstream modules.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- A child-coordinate digit is bounded by the common child total. -/
abbrev CWRecursiveChildDigit (depth : ℕ) := Fin (coarseTotal depth + 1)

/-- Coarse address alphabet for the full labelled left-plus-right child word.  This type belongs
with the quotient map itself rather than with any particular hashing client. -/
abbrev CWRecursiveCoarseAddress (depth n : ℕ) :=
  BlockAddress (fun _c ↦
    Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit depth)

/-- The weight of the labelled left child of one native parent chunk. -/
def cwRecursiveLeftChildDigit (depth : ℕ)
    (parent : PositiveWord CWBlock (2 ^ (depth + 1) - 1)) :
    CWRecursiveChildDigit depth :=
  ⟨splitWordWeight (leftChildHalf (cwChunkSplitWord (depth + 1) parent)),
    Nat.lt_succ_iff.mpr (splitWordWeight_le_coarseTotal depth _)⟩

/-- The ordered left-child coordinate word used for the three marginal type selections. -/
def cwRecursiveLeftChildWord (depth n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    Fin (n + 1) → CWRecursiveChildDigit depth :=
  fun sample ↦ cwRecursiveLeftChildDigit depth
    (positiveWordEquiv _ n word sample)

/-- The `2(n+1)` labelled child-coordinate word used by hashing and compatibility. -/
def cwRecursiveLabelledChildWord (depth n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit depth :=
  Fin.append
    (fun sample ↦ cwRecursiveLeftChildDigit depth
      (positiveWordEquiv _ n word sample))
    (fun sample ↦
      ⟨splitWordWeight (rightChildHalf
          (cwChunkSplitWord (depth + 1) (positiveWordEquiv _ n word sample))),
        Nat.lt_succ_iff.mpr (splitWordWeight_le_coarseTotal depth _)⟩)

/-- On the first half of its index range the labelled child word is the left-child word: the two
halves of `Fin.append` are the left and right labels. -/
@[simp] theorem cwRecursiveLabelledChildWord_left (depth n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (sample : Fin (n + 1)) :
    cwRecursiveLabelledChildWord depth n word (Fin.castAdd (n + 1) sample) =
      cwRecursiveLeftChildWord depth n word sample := by
  simp [cwRecursiveLabelledChildWord, cwRecursiveLeftChildWord]

end AlgebraicComplexity.Examples
