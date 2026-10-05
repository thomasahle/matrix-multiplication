/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquare
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightTypedLeaf

/-!
# The depth-one total-weight quotient is the coarsened CW square

The modern recursive Coppersmith--Winograd development and the classical square development use
two names for the same first recursive partition.  The square side coarsens an ordered pair of
CW blocks by the sum of their degrees; the recursive side turns the pair into a depth-one split
word and coarsens by its total digit weight.

This file proves that those maps agree exactly.  Consequently the support alphabet of one
depth-one total-weight chunk is the fifteen-address support `CWSquareSupport`.  This is the narrow
semantic bridge needed to apply the level-two marked-type and asymmetric-hashing API to the
recursive total-weight construction.  No tensor restriction, counting rate, or degeneration is
taken as a hypothesis here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The natural value of a native CW split digit is its classical block degree. -/
@[simp] theorem cwBlockDigit_val_eq_cwBlockDegree (block : CWBlock) :
    (cwBlockDigit block : ℕ) = cwBlockDegree block := by
  cases block <;> rfl

/-- In a depth-one chunk, position zero is the first CW block. -/
@[simp] theorem cwChunkSplitWord_one_zero (word : PositiveWord CWBlock 1) :
    cwChunkSplitWord 1 word 0 = cwBlockDigit word.1 := by
  rfl

/-- In a depth-one chunk, position one is the second CW block. -/
@[simp] theorem cwChunkSplitWord_one_one (word : PositiveWord CWBlock 1) :
    cwChunkSplitWord 1 word 1 = cwBlockDigit word.2 := by
  rfl

/-- Total split-word weight and classical square degree are the same depth-one coarsening. -/
@[simp] theorem cwChunkCoarseDigit_one_eq_cwSquareBlockDegree
    (word : PositiveWord CWBlock 1) :
    cwChunkCoarseDigit 1 word = cwSquareBlockDegree word := by
  apply Fin.ext
  rw [cwChunkCoarseDigit_val, show splitWordWeight (cwChunkSplitWord 1 word) =
      ((cwChunkSplitWord 1 word 0 : Fin 3) : ℕ) +
        ((cwChunkSplitWord 1 word 1 : Fin 3) : ℕ) by
    exact Fin.sum_univ_two _]
  simp only [cwChunkSplitWord_one_zero, cwChunkSplitWord_one_one,
    cwBlockDigit_val_eq_cwBlockDegree, cwSquareBlockDegree_val]
  exact congrArg (fun degree : ℕ ↦ degree + cwBlockDegree word.2)
    (cwBlockDigit_val_eq_cwBlockDegree (show CWBlock from word.1))

/-- Legwise, the depth-one total-weight map is literally the square degree-sum map. -/
theorem cwTotalWeightChunkCoarsening_one_eq_cwSquareDegreeMap :
    cwTotalWeightChunkCoarsening 1 = cwSquareDegreeMap := by
  funext c word
  exact cwChunkCoarseDigit_one_eq_cwSquareBlockDegree word

/-- The depth-one total-weight quotient has exactly the classical fifteen-address square support. -/
theorem cwTotalWeightCoarseSupport_one_eq_cwSquareSupport
    (K : Type u) [CommRing K] (q : ℕ) :
    ((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).support = cwSquareSupport := by
  rw [cwTotalWeightChunkCoarsening_one_eq_cwSquareDegreeMap]
  rfl

/-- Canonical identification from a total-weight support letter to the classical square support
used by the marked asymmetric-hashing API. -/
def cwTotalWeightCoarseSupportOneEquivCWSquareSupport
    (K : Type u) [CommRing K] (q : ℕ) :
    {address : CWSquareAddress // address ∈
      ((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).support} ≃
      {address : CWSquareAddress // address ∈ cwSquareSupport} where
  toFun source := ⟨source.1, by
    rw [← cwTotalWeightCoarseSupport_one_eq_cwSquareSupport K q]
    exact source.2⟩
  invFun source := ⟨source.1, by
    rw [cwTotalWeightCoarseSupport_one_eq_cwSquareSupport K q]
    exact source.2⟩
  left_inv source := Subtype.ext rfl
  right_inv source := Subtype.ext rfl

/-- The support identification does not change the underlying coarse address. -/
@[simp] theorem cwTotalWeightCoarseSupportOneEquivCWSquareSupport_val
    (K : Type u) [CommRing K] (q : ℕ)
    (source : CWTotalWeightCoarseSupport K q 1) :
    (cwTotalWeightCoarseSupportOneEquivCWSquareSupport K q source).1 = source.1 :=
  rfl

end AlgebraicComplexity.Examples
