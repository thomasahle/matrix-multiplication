/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradChunkDimension
import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeExtraction
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeaf

/-!
# Canonical matrix dimensions for Coppersmith--Winograd chunks

A chunk constituent is itself a positive-power constituent of the six-block CW partition.
This module reconstructs its unique supported base word, assigns the product of the canonical
base matrix dimensions, and proves the resulting constituent restriction.  A rational typed
leaf therefore needs only identify its stored dimension function with this canonical one; it no
longer needs to carry a separate tensor-restriction proof for every chunk letter.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-- Every chunk constituent restricts to the rectangular matrix-multiplication tensor whose
three dimensions are the explicit products of the corresponding base CW dimensions. -/
theorem cwChunkSupportedConstituent_restricts_productDimensions
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support) :
    Restricts ((cwChunkPartitionedTensor K q depth).constituent support.1)
      (matrixMultiplication (K := K)
        (positiveWordProduct (fun s ↦ (cwBlockMatrixDimensions q s.1).1)
          (2 ^ depth - 1) (cwChunkSupportedWordOfAddress K q depth support))
        (positiveWordProduct (fun s ↦ (cwBlockMatrixDimensions q s.1).2.1)
          (2 ^ depth - 1) (cwChunkSupportedWordOfAddress K q depth support))
        (positiveWordProduct (fun s ↦ (cwBlockMatrixDimensions q s.1).2.2)
          (2 ^ depth - 1) (cwChunkSupportedWordOfAddress K q depth support))) := by
  let word := cwChunkSupportedWordOfAddress K q depth support
  have hbase : ∀ s : (cwPartitionedTensor K q).support,
      Restricts ((cwPartitionedTensor K q).constituent s.1)
        (matrixMultiplication (K := K)
          (cwBlockMatrixDimensions q s.1).1
          (cwBlockMatrixDimensions q s.1).2.1
          (cwBlockMatrixDimensions q s.1).2.2) := by
    intro s
    exact cwSupportedConstituent_restricts K q s
  have hpower := Tensor.Restricts.positivePower_constituent_matrixMultiplication
    (cwPartitionedTensor K q)
    (fun s ↦ (cwBlockMatrixDimensions q s.1).1)
    (fun s ↦ (cwBlockMatrixDimensions q s.1).2.1)
    (fun s ↦ (cwBlockMatrixDimensions q s.1).2.2)
    hbase (2 ^ depth - 1) word
  change Restricts
    (((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).constituent support.1) _
  rw [← positiveSupportWordBlockAddress_cwChunkSupportedWordOfAddress
    K q depth support]
  simpa only [word] using hpower

/-- A rational leaf whose dimension table agrees with the canonical chunk dimensions obtains
all of its per-letter constituent restrictions automatically. -/
theorem cwChunk_constituent_restricts_of_leaf_dimension_eq
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c) :
    ∀ support : (cwChunkPartitionedTensor K q depth).support,
      Restricts ((cwChunkPartitionedTensor K q depth).constituent support.1)
        (matrixMultiplication (K := K)
          (leaf.dimension support .X)
          (leaf.dimension support .Y)
          (leaf.dimension support .Z)) := by
  intro support
  have hx := hdimension support .X
  have hy := hdimension support .Y
  have hz := hdimension support .Z
  rw [cwChunkConstituentDimension_X] at hx
  rw [cwChunkConstituentDimension_Y] at hy
  rw [cwChunkConstituentDimension_Z] at hz
  rw [hx, hy, hz]
  exact cwChunkSupportedConstituent_restricts_productDimensions K q depth support

end AlgebraicComplexity.Examples
