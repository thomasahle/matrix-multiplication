/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairTypedLeafCleanup
import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationCounting
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume

/-!
# Finite counting after sorted-pair compatibility cleanup

This file specializes the exact compatibility-incidence bound to the globally uniform
sorted-pair quotient of the level-two Coppersmith--Winograd alphabet.  The final support is the
literal output index of the no-hole cleanup theorem, so its cardinality can be used directly as
the copy count of a `WholeConstituentLaserVolumeStage`.

There are two certificate-facing forms:

* exact directed `Y` and `Z` competitor-incidence budgets;
* injective encodings of the competitor fibers into conditional word-type classes, whose sizes
  are controlled by the division-free multinomial identity in `ConditionalWordType`.

No fine damaged-box model, hole density, or repair-tree loss occurs on this path.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u v w

/-- The `Y` compatibility predicate on positive words of sorted-pair quotient symbols. -/
abbrev cwSortedPairCompatibilityY
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1) :=
  (cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleY
    (cwSortedPairPushforwardTargets rawTargets)

/-- The `Z` compatibility predicate on positive words of sorted-pair quotient symbols. -/
abbrev cwSortedPairCompatibilityZ
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1) :=
  (cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleZ
    (cwSortedPairPushforwardTargets rawTargets)

/-- Support after the quotient `Y` unique-compatibility zero-out. -/
noncomputable def cwSortedPairYIsolatedSupport
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))) :=
  compatibilityIsolatedSupport ambient .Y
    (cwSortedPairCompatibilityY n partAt rawTargets)

/-- Final support after the quotient `Y` and then `Z` unique-compatibility zero-outs. -/
noncomputable def cwSortedPairYZIsolatedSupport
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))) :=
  compatibilityIsolatedSupport
    (cwSortedPairYIsolatedSupport n partAt rawTargets ambient) .Z
    (cwSortedPairCompatibilityZ n partAt rawTargets)

/-- Exact number of directed `Y` competitor incidences before `Y` cleanup. -/
noncomputable def cwSortedPairYCompetitorIncidence
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))) : ℕ :=
  compatibilityCompetitorIncidence ambient .Y
    (cwSortedPairCompatibilityY n partAt rawTargets)

/-- Exact number of directed `Z` competitor incidences after `Y` cleanup. -/
noncomputable def cwSortedPairZCompetitorIncidence
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))) : ℕ :=
  compatibilityCompetitorIncidence
    (cwSortedPairYIsolatedSupport n partAt rawTargets ambient) .Z
    (cwSortedPairCompatibilityZ n partAt rawTargets)

/-- Exact finite quotient count: the ambient support is covered by the final isolated support
and the two directed competitor-incidence families. -/
theorem cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_incidences
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))) :
    ambient.card ≤
      (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card +
        cwSortedPairYCompetitorIncidence n partAt rawTargets ambient +
        cwSortedPairZCompetitorIncidence n partAt rawTargets ambient := by
  simpa only [cwSortedPairYZIsolatedSupport, cwSortedPairYIsolatedSupport,
    cwSortedPairYCompetitorIncidence, cwSortedPairZCompetitorIncidence] using
    (card_le_card_YZCompatibilityIsolatedSupport_add_incidences
      ambient (cwSortedPairCompatibilityY n partAt rawTargets)
        (cwSortedPairCompatibilityZ n partAt rawTargets))

/-- Certificate-budget form of the exact quotient count. -/
theorem cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_budgets
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (budgetY budgetZ : ℕ)
    (hbudgetY : cwSortedPairYCompetitorIncidence
      n partAt rawTargets ambient ≤ budgetY)
    (hbudgetZ : cwSortedPairZCompetitorIncidence
      n partAt rawTargets ambient ≤ budgetZ) :
    ambient.card ≤
      (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card +
        budgetY + budgetZ := by
  simpa only [cwSortedPairYZIsolatedSupport, cwSortedPairYIsolatedSupport,
    cwSortedPairYCompetitorIncidence, cwSortedPairZCompetitorIncidence] using
    (card_le_card_YZCompatibilityIsolatedSupport_add_budgets
      ambient (cwSortedPairCompatibilityY n partAt rawTargets)
        (cwSortedPairCompatibilityZ n partAt rawTargets)
      budgetY budgetZ hbudgetY hbudgetZ)

/-- Half-density form: exact competitor budgets totaling at most half the hashed ambient family
leave at least half as many whole quotient constituents. -/
theorem cwSortedPair_card_ambient_le_two_mul_card_YZIsolatedSupport
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (budgetY budgetZ : ℕ)
    (hbudgetY : cwSortedPairYCompetitorIncidence
      n partAt rawTargets ambient ≤ budgetY)
    (hbudgetZ : cwSortedPairZCompetitorIncidence
      n partAt rawTargets ambient ≤ budgetZ)
    (hhalf : 2 * (budgetY + budgetZ) ≤ ambient.card) :
    ambient.card ≤
      2 * (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card := by
  simpa only [cwSortedPairYZIsolatedSupport, cwSortedPairYIsolatedSupport,
    cwSortedPairYCompetitorIncidence, cwSortedPairZCompetitorIncidence] using
    (card_le_two_mul_card_YZCompatibilityIsolatedSupport
      ambient (cwSortedPairCompatibilityY n partAt rawTargets)
        (cwSortedPairCompatibilityZ n partAt rawTargets)
      budgetY budgetZ hbudgetY hbudgetZ hhalf)

/-! ## Exact conditional-type competitor counts -/

/-- If every quotient `Y` competitor fiber injects into a supplied conditional type class, the
sum of those exact type-class sizes bounds the full `Y` incidence. -/
theorem cwSortedPairYCompetitorIncidence_le_sum_conditionalTypeCounts
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    {U Z : Type v} [Fintype U] [Fintype Z] {samples : ℕ}
    (encoding : ∀ address,
      ConditionalCompetitorEncoding ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets)
        address U Z samples) :
    cwSortedPairYCompetitorIncidence n partAt rawTargets ambient ≤
      ∑ address ∈ ambient,
        (WordType.conditionalTypeClass
          (encoding address).source (encoding address).jointType).card := by
  classical
  unfold cwSortedPairYCompetitorIncidence compatibilityCompetitorIncidence
  apply Finset.sum_le_sum
  intro address _haddress
  exact (encoding address).card_competitors_le_card_conditionalTypeClass

/-- The corresponding conditional-type bound for the `Z` pass, measured on the support that
survived `Y` isolation. -/
theorem cwSortedPairZCompetitorIncidence_le_sum_conditionalTypeCounts
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    {U Z : Type v} [Fintype U] [Fintype Z] {samples : ℕ}
    (encoding : ∀ address,
      ConditionalCompetitorEncoding
        (cwSortedPairYIsolatedSupport n partAt rawTargets ambient) .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets)
        address U Z samples) :
    cwSortedPairZCompetitorIncidence n partAt rawTargets ambient ≤
      ∑ address ∈ cwSortedPairYIsolatedSupport n partAt rawTargets ambient,
        (WordType.conditionalTypeClass
          (encoding address).source (encoding address).jointType).card := by
  classical
  unfold cwSortedPairZCompetitorIncidence compatibilityCompetitorIncidence
  apply Finset.sum_le_sum
  intro address _haddress
  exact (encoding address).card_competitors_le_card_conditionalTypeClass

/-- Quotient-specialized method-of-types count.  After clients supply the two injective
competitor classifications, the only losses are the displayed exact conditional type classes. -/
theorem cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_conditionalTypeCounts
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    {UY ZY : Type v} [Fintype UY] [Fintype ZY] {samplesY : ℕ}
    {UZ ZZ : Type w} [Fintype UZ] [Fintype ZZ] {samplesZ : ℕ}
    (encodingY : ∀ address,
      ConditionalCompetitorEncoding ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets)
        address UY ZY samplesY)
    (encodingZ : ∀ address,
      ConditionalCompetitorEncoding
        (cwSortedPairYIsolatedSupport n partAt rawTargets ambient) .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets)
        address UZ ZZ samplesZ) :
    ambient.card ≤
      (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card +
        (∑ address ∈ ambient,
          (WordType.conditionalTypeClass
            (encodingY address).source (encodingY address).jointType).card) +
        (∑ address ∈ cwSortedPairYIsolatedSupport n partAt rawTargets ambient,
          (WordType.conditionalTypeClass
            (encodingZ address).source (encodingZ address).jointType).card) := by
  apply cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_budgets
    n partAt rawTargets ambient
  · exact cwSortedPairYCompetitorIncidence_le_sum_conditionalTypeCounts
      n partAt rawTargets ambient encodingY
  · exact cwSortedPairZCompetitorIncidence_le_sum_conditionalTypeCounts
      n partAt rawTargets ambient encodingZ

/-! ## Hashing and whole-constituent assembly -/

/-- Compose any exact hashing lower bound with the half-density compatibility estimate.  This is
the division-free copy-growth inequality consumed by the no-hole asymptotic sequence: hashing
loss is multiplied only by the fixed factor two. -/
theorem cwSortedPair_hashCount_le_two_mul_hashLoss_mul_card_YZIsolatedSupport
    {Part : Type u} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hashCount hashLoss budgetY budgetZ : ℕ)
    (hhash : hashCount ≤ hashLoss * ambient.card)
    (hbudgetY : cwSortedPairYCompetitorIncidence
      n partAt rawTargets ambient ≤ budgetY)
    (hbudgetZ : cwSortedPairZCompetitorIncidence
      n partAt rawTargets ambient ≤ budgetZ)
    (hhalf : 2 * (budgetY + budgetZ) ≤ ambient.card) :
    hashCount ≤ (2 * hashLoss) *
      (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card := by
  have hretained := cwSortedPair_card_ambient_le_two_mul_card_YZIsolatedSupport
    n partAt rawTargets ambient budgetY budgetZ hbudgetY hbudgetZ hhalf
  calc
    hashCount ≤ hashLoss * ambient.card := hhash
    _ ≤ hashLoss *
        (2 * (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card) :=
      Nat.mul_le_mul_left hashLoss hretained
    _ = (2 * hashLoss) *
        (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card := by ring

/-- Package a restriction to the final sorted-pair isolated support as an exact no-hole finite
laser-volume stage.  The copy count is definitionally the final support cardinality. -/
noncomputable def cwSortedPairWholeConstituentLaserVolumeStage
    (K : Type v) [CommSemiring K]
    {Source : Leg → Type w} [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {n : ℕ} (finalSupport : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (source : Tensor3 K Source) (xSize ySize zSize : ℕ)
    (hrestricts : Restricts source
      (Tensor.indexedDirectSum (fun _address : finalSupport ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    WholeConstituentLaserVolumeStage K source finalSupport.card xSize ySize zSize where
  I := finalSupport
  card_I := by simp
  source_restricts := by
    simpa only [matrixMultiplicationDirectSum] using hrestricts

end AlgebraicComplexity.Examples
