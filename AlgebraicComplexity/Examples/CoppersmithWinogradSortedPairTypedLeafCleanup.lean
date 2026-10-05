/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairCompatibility
import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordQuotientTypedLeaf

/-!
# Sorted-pair compatibility cleanup to fine rational typed leaves

This module closes the finite semantic bridge from quotient-alphabet compatibility cleanup to
the original fine Coppersmith--Winograd typed leaf.  Equality of the three quotient-label
profiles conditional on the ordered CW shape determines the full joint quotient type.  The
coarse constituent can therefore be projected to a fine support word of the prescribed rational
type and hence to the same rectangular matrix-multiplication tensor as before coarsening.

The final composition theorem works directly with the output of sorted-pair `Y/Z` compatibility
isolation.  Since that cleanup zeros quotient variables atomically, every retained summand is a
whole quotient constituent: its internal hole set is empty.  The sole quantitative finite
obligation left to the certificate client is consequently the cardinality of the final isolated
support, rather than a hole-density or repair-tree budget.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- The profile of quotient labels conditional on their ordered CW shape. -/
noncomputable def cwSortedPairShapeConditionalProfile
    (K : Type u) [CommRing K] (q : ℕ)
    (counts : CWSortedPairCoarseSupport K q → ℕ) (c : Leg) :
    ((Leg → ℕ) × SplitWord 1) → ℕ :=
  WordType.mappedType
    (fun address : CWSortedPairCoarseSupport K q ↦
      (cwSortedPairSupportedShape K q address, address.1 c)) counts

/-- Equality of all three shape-conditional quotient profiles forces a quotient support word to
have the prescribed full joint type. -/
theorem cwSortedPair_mem_positiveTypeClass_of_shapeConditionalProfiles
    (K : Type u) [CommRing K] (q r : ℕ)
    (word : PositiveWord (CWSortedPairCoarseSupport K q) r)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (hprofiles : ∀ c,
      cwSortedPairShapeConditionalProfile K q
          (WordType.multiplicity
            (positiveWordEquiv (CWSortedPairCoarseSupport K q) r word)) c =
        cwSortedPairShapeConditionalProfile K q targetType c) :
    word ∈ positiveTypeClass (CWSortedPairCoarseSupport K q) r targetType := by
  rw [mem_positiveTypeClass]
  exact cwSortedPair_jointType_eq_of_conditionalProfiles K q _ _ hprofiles

/-- A pair-sorted coarse constituent with the prescribed `alpha` and conditional quotient
profiles contains the original fine rational typed leaf, with exactly its original matrix
dimensions. -/
theorem cwSortedPair_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeConditionalProfiles
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hconstituent : ∀ s : (cwChunkPartitionedTensor K q 1).support,
      Restricts ((cwChunkPartitionedTensor K q 1).constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {r k : ℕ}
    (coarseWord : PositiveWord (CWSortedPairCoarseSupport K q) r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q 1).support (r + 1))
    (hprofiles : ∀ c,
      cwSortedPairShapeConditionalProfile K q
          (WordType.multiplicity
            (positiveWordEquiv (CWSortedPairCoarseSupport K q) r coarseWord)) c =
        cwSortedPairShapeConditionalProfile K q
          (WordType.mappedType
            ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
              cwSortedPairChunkCoarsening)
            (WordType.proportionalCounts leaf.profile.count k)) c) :
    Restricts
      (((cwChunkPartitionedTensor K q 1).coarsenedPositivePower
          cwSortedPairChunkCoarsening r).constituent
        (positiveSupportWordBlockAddress (CWSortedPairCoarseSupport K q) r coarseWord))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) := by
  classical
  let first : CWSortedPairCoarseSupport K q :=
    positiveWordEquiv (CWSortedPairCoarseSupport K q) r coarseWord 0
  have hfirst := first.2
  change first.1 ∈
    ((cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening).support at hfirst
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at hfirst
  obtain ⟨fine, hfine, _hmap⟩ := hfirst
  letI : Nonempty (cwChunkPartitionedTensor K q 1).support :=
    ⟨⟨fine, hfine⟩⟩
  apply RationalTypedLeaf.coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
      (cwChunkPartitionedTensor K q 1) cwSortedPairChunkCoarsening leaf hconstituent
      coarseWord hlegal
  exact cwSortedPair_mem_positiveTypeClass_of_shapeConditionalProfiles
    K q r coarseWord _ hprofiles

/-- Copy-preserving indexed form of the conditional-profile typed-leaf bridge. -/
theorem cwSortedPair_indexedDirectSum_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeConditionalProfiles
    (K : Type u) [CommRing K] (q : ℕ)
    {I : Type*} [Fintype I]
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hconstituent : ∀ s : (cwChunkPartitionedTensor K q 1).support,
      Restricts ((cwChunkPartitionedTensor K q 1).constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {r k : ℕ}
    (coarseWord : I → PositiveWord (CWSortedPairCoarseSupport K q) r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q 1).support (r + 1))
    (hprofiles : ∀ i c,
      cwSortedPairShapeConditionalProfile K q
          (WordType.multiplicity
            (positiveWordEquiv (CWSortedPairCoarseSupport K q) r (coarseWord i))) c =
        cwSortedPairShapeConditionalProfile K q
          (WordType.mappedType
            ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
              cwSortedPairChunkCoarsening)
            (WordType.proportionalCounts leaf.profile.count k)) c) :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦
        ((cwChunkPartitionedTensor K q 1).coarsenedPositivePower
          cwSortedPairChunkCoarsening r).constituent
            (positiveSupportWordBlockAddress
              (CWSortedPairCoarseSupport K q) r (coarseWord i))))
      (Tensor.indexedDirectSum (fun _i : I ↦
        matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k))) := by
  apply Restricts.indexedDirectSum
  intro i
  exact cwSortedPair_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeConditionalProfiles
    K q leaf hconstituent (coarseWord i) hlegal (hprofiles i)

/-- End-to-end finite semantic adapter for sorted-pair quotient compatibility cleanup.  Each
final isolated address is required only to expose a support word with the prescribed
shape-conditional profiles.  Conditional rigidity reconstructs its full joint type, after which
the rational typed-leaf theorem projects the whole quotient constituent to the original fine
matrix-multiplication leaf.  Because quotient variables were zeroed atomically, there are no
internal holes and the output index is exactly the final isolated support. -/
theorem cwSortedPairFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_shapeConditionalProfiles
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) ↦
        address .X) ambient)
    (hpassesY : ∀ address ∈ ambient,
      let model := cwSortedPairFeatureCompatibilityModel n partAt
      let targets := cwSortedPairPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol)
    (hpassesZ : ∀ address ∈ compatibilityIsolatedSupport ambient .Y
        ((cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleY
          (cwSortedPairPushforwardTargets rawTargets)),
      let model := cwSortedPairFeatureCompatibilityModel n partAt
      let targets := cwSortedPairPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hconstituent : ∀ s : (cwChunkPartitionedTensor K q 1).support,
      Restricts ((cwChunkPartitionedTensor K q 1).constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {k : ℕ}
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q 1).support (n + 1))
    (hjoint : ∀ address : compatibilityIsolatedSupport
        (compatibilityIsolatedSupport ambient .Y
          ((cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleY
            (cwSortedPairPushforwardTargets rawTargets))) .Z
          ((cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleZ
            (cwSortedPairPushforwardTargets rawTargets)),
      ∃ coarseWord : PositiveWord (CWSortedPairCoarseSupport K q) n,
        positiveSupportWordBlockAddress
            (CWSortedPairCoarseSupport K q) n coarseWord = address.1 ∧
          ∀ c,
            cwSortedPairShapeConditionalProfile K q
                (WordType.multiplicity
                  (positiveWordEquiv
                    (CWSortedPairCoarseSupport K q) n coarseWord)) c =
              cwSortedPairShapeConditionalProfile K q
                (WordType.mappedType
                  ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
                    cwSortedPairChunkCoarsening)
                  (WordType.proportionalCounts leaf.profile.count k)) c) :
    let Q := (cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening
    let P := (Q.positivePower n).withSupport ambient
    let model := cwSortedPairFeatureCompatibilityModel n partAt
    let targets := cwSortedPairPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    Restricts P.realize
      (Tensor.indexedDirectSum (fun _address : zSupport ↦
        matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k))) := by
  classical
  let Q := (cwChunkPartitionedTensor K q 1).coarsen
    cwSortedPairChunkCoarsening
  let P := (Q.positivePower n).withSupport ambient
  let model := cwSortedPairFeatureCompatibilityModel n partAt
  let targets := cwSortedPairPushforwardTargets rawTargets
  let ySupport := compatibilityIsolatedSupport ambient .Y
    (model.FeatureCompatibleY targets)
  let zSupport := compatibilityIsolatedSupport ySupport .Z
    (model.FeatureCompatibleZ targets)
  have hcleanup : Restricts P.realize
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ P.constituent address.1)) := by
    simpa [Q, P, model, targets, ySupport, zSupport] using
      cwSortedPairFeatureYZCompatibilityCleanup_to_indexedDirectSum
        K q n partAt rawTargets ambient hambient hX hpassesY hpassesZ
  apply hcleanup.trans
  apply Restricts.indexedDirectSum
  intro address
  obtain ⟨coarseWord, hword, hprofiles⟩ := hjoint address
  have hleaf :=
    cwSortedPair_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeConditionalProfiles
      K q leaf hconstituent coarseWord hlegal hprofiles
  change Restricts ((Q.positivePower n).constituent address.1) _
  rw [← hword]
  exact hleaf

end AlgebraicComplexity.Examples
