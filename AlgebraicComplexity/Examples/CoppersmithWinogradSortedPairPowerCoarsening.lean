/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotientTypedLeaf
import AlgebraicComplexity.Tensor.PartitionedCoarseningPower

/-!
# Power/coarsening coherence for the sorted-pair CW quotient

This file specializes the generic distributivity equivalence to the globally consistent
level-two reversal quotient.  Its main restriction starts with the representation used by
quotient-level hashing, namely the positive power of the already coarsened CW partition, and
returns the entire fine type-selected tensor used by the rational typed-leaf theorem.

No quotient-fiber cardinality is charged: the result preserves a whole selected tensor, not one
chosen lift of each quotient word.  Thus an outer retained-address count and the subsequent fine
typed-leaf (`E2`) count remain hierarchical multiplicative factors.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The quotient-first and after-power-coarsened exact type selections for the pair-sorted CW
partition are canonically isomorphic. -/
theorem cwSortedPair_selectCoarsenedPositiveTypes_isomorphic_afterPowerCoarsenedTypes
    (K : Type u) [CommRing K] (q n : ℕ)
    (coarseType : ∀ _c, SplitWord 1 → ℕ) :
    Isomorphic
      (((cwChunkPartitionedTensor K q 1).selectCoarsenedPositiveTypes
        cwSortedPairChunkCoarsening n coarseType).realize)
      (((((cwChunkPartitionedTensor K q 1).positivePower n).coarsen
          (fun c ↦ positiveWordMap (cwSortedPairChunkCoarsening c) n)).select
        (fun c word ↦ word ∈ positiveTypeClass (SplitWord 1) n
          (coarseType c))).realize) :=
  Isomorphic.selectCoarsenedPositiveTypes_to_afterPowerCoarsenedTypes
    (cwChunkPartitionedTensor K q 1) cwSortedPairChunkCoarsening n coarseType

/-- A quotient-first pair-sorted exact type selection restricts to the entire original fine
type selection.  In particular, the inner rational typed-leaf exponent and dimensions are
unchanged. -/
theorem cwSortedPair_selectCoarsenedPositiveMappedTypes_restricts_fineSelectedTypes
    (K : Type u) [CommRing K] (q n : ℕ)
    (fineType : ∀ _c, PositiveWord CWBlock 1 → ℕ) :
    Restricts
      (((cwChunkPartitionedTensor K q 1).selectCoarsenedPositiveTypes
        cwSortedPairChunkCoarsening n
        (fun c ↦ WordType.mappedType
          (cwSortedPairChunkCoarsening c) (fineType c))).realize)
      ((((cwChunkPartitionedTensor K q 1).positivePower n).select
        (fun c word ↦ word ∈ positiveTypeClass (PositiveWord CWBlock 1) n
          (fineType c))).realize) :=
  Restricts.selectCoarsenedPositiveMappedTypes_to_fineTypes
    (cwChunkPartitionedTensor K q 1) cwSortedPairChunkCoarsening n fineType

/-- Indexed copy-preserving form of the quotient-first pair-sorted bridge. -/
theorem cwSortedPair_indexedDirectSum_selectCoarsenedPositiveMappedTypes_restricts_fineSelectedTypes
    {I : Type*} [Fintype I]
    (K : Type u) [CommRing K] (q n : ℕ)
    (fineType : ∀ _c, PositiveWord CWBlock 1 → ℕ) :
    Restricts
      (Tensor.indexedDirectSum (fun _i : I ↦
        ((cwChunkPartitionedTensor K q 1).selectCoarsenedPositiveTypes
          cwSortedPairChunkCoarsening n
          (fun c ↦ WordType.mappedType
            (cwSortedPairChunkCoarsening c) (fineType c))).realize))
      (Tensor.indexedDirectSum (fun _i : I ↦
        (((cwChunkPartitionedTensor K q 1).positivePower n).select
          (fun c word ↦ word ∈ positiveTypeClass (PositiveWord CWBlock 1) n
            (fineType c))).realize)) :=
  Restricts.indexedDirectSum_selectCoarsenedPositiveMappedTypes_to_fineTypes
    (I := I) (cwChunkPartitionedTensor K q 1)
      cwSortedPairChunkCoarsening n fineType

end AlgebraicComplexity.Examples
