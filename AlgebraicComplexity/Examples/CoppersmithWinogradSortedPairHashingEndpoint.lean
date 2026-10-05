/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairCompatibilityHashing

/-!
# Finite sorted-pair hashing endpoint

This module treats a support selected by the support-aware affine hashing theorem as the ambient
partition for the ordinary `Y/Z` compatibility zero-outs.  Unequal coarse legal triples have
already been isolated; the remaining equal-triple incidences are charged by explicit exact
budgets.  The semantic endpoint is a restriction to a direct sum of whole rational typed leaves,
with both the exact additive count and its half-density consequence.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- Forget the proof that a hash-selected quotient address belongs to the positive-power
support. -/
noncomputable def cwSortedPairSelectedAddressSupport
    (K : Type u) [CommRing K] (q n : ℕ)
    (selected : Finset (CWSortedPairPowerSupport K q n)) :
    Finset (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)) := by
  classical
  exact selected.image Subtype.val

@[simp] theorem card_cwSortedPairSelectedAddressSupport
    (K : Type u) [CommRing K] (q n : ℕ)
    (selected : Finset (CWSortedPairPowerSupport K q n)) :
    (cwSortedPairSelectedAddressSupport K q n selected).card = selected.card := by
  classical
  exact Finset.card_image_of_injOn Subtype.val_injective.injOn

/-- Every hash-selected address remains in the quotient positive-power support. -/
theorem cwSortedPairSelectedAddressSupport_subset
    (K : Type u) [CommRing K] (q n : ℕ)
    (selected : Finset (CWSortedPairPowerSupport K q n)) :
    cwSortedPairSelectedAddressSupport K q n selected ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support := by
  classical
  intro address haddress
  obtain ⟨source, _hsource, rfl⟩ := Finset.mem_image.mp haddress
  exact source.2

/-- On a family isolated against the union of catchable `Y/Z` alternatives, every remaining
raw-compatible `Y` pair is either diagonal or has the same complete coarse legal triple. -/
theorem eq_or_YResidual_of_cwSortedPairYZCatchableIsolation
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (common selected : Finset (CWSortedPairPowerSupport K q n))
    (hcommon : selected ⊆ common)
    (hisolated : selected ⊆ ProgressionHash.Seed.compatibilityIsolatedTargets common
      (cwSortedPairCatchableCompatibilityYZ encoding K q n partAt rawTargets))
    {target other : CWSortedPairPowerSupport K q n}
    (htarget : target ∈ selected) (hother : other ∈ selected)
    (hcompatible :
      cwSortedPairCompatibilityY n partAt rawTargets (target.1 .Y) other.1) :
    other = target ∨
      cwSortedPairLegalTriple encoding K q n other =
        cwSortedPairLegalTriple encoding K q n target := by
  by_cases heq : cwSortedPairLegalTriple encoding K q n other =
      cwSortedPairLegalTriple encoding K q n target
  · exact Or.inr heq
  · left
    have htargetIsolated := (ProgressionHash.Seed.mem_compatibilityIsolatedTargets
      common (cwSortedPairCatchableCompatibilityYZ encoding K q n partAt rawTargets)
      target).mp (hisolated htarget)
    exact htargetIsolated.2 other (hcommon hother) (Or.inl ⟨hcompatible, heq⟩)

/-- The same residual-only conclusion for raw `Z` compatibility. -/
theorem eq_or_ZResidual_of_cwSortedPairYZCatchableIsolation
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part] (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (common selected : Finset (CWSortedPairPowerSupport K q n))
    (hcommon : selected ⊆ common)
    (hisolated : selected ⊆ ProgressionHash.Seed.compatibilityIsolatedTargets common
      (cwSortedPairCatchableCompatibilityYZ encoding K q n partAt rawTargets))
    {target other : CWSortedPairPowerSupport K q n}
    (htarget : target ∈ selected) (hother : other ∈ selected)
    (hcompatible :
      cwSortedPairCompatibilityZ n partAt rawTargets (target.1 .Z) other.1) :
    other = target ∨
      cwSortedPairLegalTriple encoding K q n other =
        cwSortedPairLegalTriple encoding K q n target := by
  by_cases heq : cwSortedPairLegalTriple encoding K q n other =
      cwSortedPairLegalTriple encoding K q n target
  · exact Or.inr heq
  · left
    have htargetIsolated := (ProgressionHash.Seed.mem_compatibilityIsolatedTargets
      common (cwSortedPairCatchableCompatibilityYZ encoding K q n partAt rawTargets)
      target).mp (hisolated htarget)
    exact htargetIsolated.2 other (hcommon hother) (Or.inr ⟨hcompatible, heq⟩)

/-- A fixed hash-selected quotient family restricts to its final `Y/Z`-isolated direct sum of
whole rational typed leaves.  The result simultaneously records the exact additive cardinality
loss, the half-density bound, and a generic hash-count composition. -/
theorem cwSortedPairHashSelected_to_matrixMultiplicationDirectSum
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (selected : Finset (CWSortedPairPowerSupport K q n))
    (hX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) ↦
        address .X) (cwSortedPairSelectedAddressSupport K q n selected))
    (hpassesY : ∀ address ∈ cwSortedPairSelectedAddressSupport K q n selected,
      let model := cwSortedPairFeatureCompatibilityModel n partAt
      let targets := cwSortedPairPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol)
    (hpassesZ : ∀ address ∈ cwSortedPairYIsolatedSupport n partAt rawTargets
        (cwSortedPairSelectedAddressSupport K q n selected),
      let model := cwSortedPairFeatureCompatibilityModel n partAt
      let targets := cwSortedPairPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol)
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hconstituent : ∀ s : (cwChunkPartitionedTensor K q 1).support,
      Restricts ((cwChunkPartitionedTensor K q 1).constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {k : ℕ}
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q 1).support (n + 1))
    (hjoint : ∀ address : cwSortedPairYZIsolatedSupport n partAt rawTargets
        (cwSortedPairSelectedAddressSupport K q n selected),
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
                  (WordType.proportionalCounts leaf.profile.count k)) c)
    (budgetY budgetZ : ℕ)
    (hbudgetY : cwSortedPairYCompetitorIncidence n partAt rawTargets
      (cwSortedPairSelectedAddressSupport K q n selected) ≤ budgetY)
    (hbudgetZ : cwSortedPairZCompetitorIncidence n partAt rawTargets
      (cwSortedPairSelectedAddressSupport K q n selected) ≤ budgetZ)
    (hhalf : 2 * (budgetY + budgetZ) ≤ selected.card)
    (hashCount hashLoss : ℕ)
    (hhash : hashCount ≤ hashLoss * selected.card) :
    let ambient := cwSortedPairSelectedAddressSupport K q n selected
    let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
    Restricts
        (((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
        (Tensor.indexedDirectSum (fun _address : finalSupport ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) ∧
      selected.card ≤ finalSupport.card + budgetY + budgetZ ∧
      selected.card ≤ 2 * finalSupport.card ∧
      hashCount ≤ (2 * hashLoss) * finalSupport.card := by
  classical
  let ambient := cwSortedPairSelectedAddressSupport K q n selected
  let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
  have hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support := by
    exact cwSortedPairSelectedAddressSupport_subset K q n selected
  have hrestricts : Restricts
      (((((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
      (Tensor.indexedDirectSum (fun _address : finalSupport ↦
        matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k))) := by
    change Restricts _
      (Tensor.indexedDirectSum (fun _address :
        compatibilityIsolatedSupport
          (compatibilityIsolatedSupport ambient .Y
            ((cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleY
              (cwSortedPairPushforwardTargets rawTargets))) .Z
          ((cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleZ
            (cwSortedPairPushforwardTargets rawTargets)) ↦
        matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k)))
    exact
      (cwSortedPairFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_shapeConditionalProfiles
        K q n partAt rawTargets ambient hambient hX hpassesY hpassesZ
        leaf hconstituent hlegal hjoint)
  have hcardAmbient : ambient.card = selected.card := by
    exact card_cwSortedPairSelectedAddressSupport K q n selected
  have hhalfAmbient : 2 * (budgetY + budgetZ) ≤ ambient.card := by
    simpa only [hcardAmbient] using hhalf
  have hadd := cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_budgets
    n partAt rawTargets ambient budgetY budgetZ hbudgetY hbudgetZ
  have htwo := cwSortedPair_card_ambient_le_two_mul_card_YZIsolatedSupport
    n partAt rawTargets ambient budgetY budgetZ hbudgetY hbudgetZ hhalfAmbient
  have hhashAmbient : hashCount ≤ hashLoss * ambient.card := by
    simpa only [hcardAmbient] using hhash
  have hcomposed := cwSortedPair_hashCount_le_two_mul_hashLoss_mul_card_YZIsolatedSupport
    n partAt rawTargets ambient hashCount hashLoss budgetY budgetZ
    hhashAmbient hbudgetY hbudgetZ hhalfAmbient
  exact ⟨hrestricts, by simpa only [hcardAmbient] using hadd,
    by simpa only [hcardAmbient] using htwo, hcomposed⟩

/-- Package the uniform typed-leaf restriction produced above as a no-hole finite laser-volume
stage.  Its copy count is exactly the final isolated-support cardinality. -/
noncomputable def cwSortedPairHashSelectedWholeConstituentLaserVolumeStage
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (selected : Finset (CWSortedPairPowerSupport K q n))
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (k : ℕ)
    (hrestricts :
      let ambient := cwSortedPairSelectedAddressSupport K q n selected
      let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
      Restricts
        (((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
        (Tensor.indexedDirectSum (fun _address : finalSupport ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k)))) :
    let ambient := cwSortedPairSelectedAddressSupport K q n selected
    let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
    WholeConstituentLaserVolumeStage K
      (((((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
      finalSupport.card
      (leaf.dimensionProduct .X ^ k)
      (leaf.dimensionProduct .Y ^ k)
      (leaf.dimensionProduct .Z ^ k) := by
  classical
  let ambient := cwSortedPairSelectedAddressSupport K q n selected
  let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
  exact cwSortedPairWholeConstituentLaserVolumeStage K finalSupport
    (((((cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
    (leaf.dimensionProduct .X ^ k)
    (leaf.dimensionProduct .Y ^ k)
    (leaf.dimensionProduct .Z ^ k) hrestricts

end AlgebraicComplexity.Examples
