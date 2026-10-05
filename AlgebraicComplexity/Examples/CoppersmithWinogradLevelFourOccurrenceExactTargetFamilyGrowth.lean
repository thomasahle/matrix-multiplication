/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.FiniteFamilyTail
import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceExactTargetGrowth

set_option autoImplicit false

/-!
# One exact-target cutoff for a finite level-four node family

The fixed-node target-growth theorem is uniform in marked references and logical legs but initially
has a node-dependent cutoff.  This module takes the finite maximum over an arbitrary finite family
of level-four nodes.  Every node may have its own root, region, parent shape, coordinate order, and
orientation; orientations may repeat.

No generated certificate, compatibility incidence, tensor repair, retained-exponent floor, or
numerical endpoint is used.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- **Finite-family input-hole bound.**  At any fixed positive tolerance and fixed repair budget,
one cutoff works simultaneously for every positive node in an arbitrary finite level-four family,
every marked reference, and all three logical legs.  The target on the right is the actual native
recursive exact-target fiber, not an assumed cardinality surrogate. -/
theorem eventually_budget_mul_card_levelFourOccurrenceInputProfileHoles_le_exactTarget_finiteFamily
    {ι : Type*} [Finite ι]
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : ι → CoordinateOrder) (sigma : ι → Orientation)
    (root region : ι → Fin 6) (parent : ι → Fin positiveLevelFourShapeCount)
    (horder : ∀ i, CoordinateOrder.AgreesWithOrientation (order i) (sigma i))
    (hvalid : ∀ i,
      LevelFourChildRowsValid top betaThree (root i) (region i) (parent i) (sigma i))
    (hboundary : ∀ i, FixedParentSlotBoundaryValid
      top betaThree (order i) (root i).val (region i).val (parent i).val)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (budget : ℕ) :
    ∃ cutoff : ℕ,
      ∀ i,
      0 < levelFourParentSamples top (root i) (region i) (parent i) →
      ∀ k n : ℕ, cutoff ≤ k → ∀ _hk : 0 < k,
      ∀ (hsamples :
          WordType.profileMass
              (levelFourOccurrenceSourceProfile top (root i) (region i) (parent i)) * k = n + 1)
        (reference : CWRecursiveCoarseAddress 2 n),
        reference ∈
            cwRecursiveRelaxedMarkedCoarseSupport
              (levelFourOccurrenceParentTerm top betaThree
                (root i) (region i) (parent i) (sigma i) (hvalid i) k)
              (Equiv.refl Leg)
              (levelFourOccurrenceSplitType top betaThree
                (root i) (region i) (parent i) (sigma i) (hvalid i) k n hsamples) →
      ∀ logicalLeg : Leg,
        budget *
            (cwRecursiveInputProfileHoles
              (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
              (levelFourOccurrenceParentTerm top betaThree
                (root i) (region i) (parent i) (sigma i) (hvalid i) k)
              (levelFourOccurrenceParentTerm_multiplicity_eq_succ
                top betaThree (root i) (region i) (parent i) (sigma i)
                (hvalid i) k n hsamples)
              epsilon
              (RecursiveOccurrenceTargetData.toCompatibilityTargets
                (cwProportionalRecursiveOccurrenceTargetData
                  (levelFourOccurrenceTargetData top betaThree (order i) (sigma i) (horder i)
                    (root i) (region i) (parent i) (hvalid i) (hboundary i)) k))
              reference logicalLeg).card ≤
          (cwRecursiveExactTargetFiberParts
            (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
            (RecursiveOccurrenceTargetData.toCompatibilityTargets
              (cwProportionalRecursiveOccurrenceTargetData
                (levelFourOccurrenceTargetData top betaThree (order i) (sigma i) (horder i)
                  (root i) (region i) (parent i) (hvalid i) (hboundary i)) k))
            reference logicalLeg).card := by
  classical
  let P : ι → ℕ → Prop := fun i k ↦
    0 < levelFourParentSamples top (root i) (region i) (parent i) →
    ∀ n : ℕ, 0 < k →
    ∀ (hsamples :
        WordType.profileMass
            (levelFourOccurrenceSourceProfile top (root i) (region i) (parent i)) * k = n + 1)
      (reference : CWRecursiveCoarseAddress 2 n),
      reference ∈
          cwRecursiveRelaxedMarkedCoarseSupport
            (levelFourOccurrenceParentTerm top betaThree
              (root i) (region i) (parent i) (sigma i) (hvalid i) k)
            (Equiv.refl Leg)
            (levelFourOccurrenceSplitType top betaThree
              (root i) (region i) (parent i) (sigma i) (hvalid i) k n hsamples) →
    ∀ logicalLeg : Leg,
      budget *
          (cwRecursiveInputProfileHoles
            (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
            (levelFourOccurrenceParentTerm top betaThree
              (root i) (region i) (parent i) (sigma i) (hvalid i) k)
            (levelFourOccurrenceParentTerm_multiplicity_eq_succ
              top betaThree (root i) (region i) (parent i) (sigma i)
              (hvalid i) k n hsamples)
            epsilon
            (RecursiveOccurrenceTargetData.toCompatibilityTargets
              (cwProportionalRecursiveOccurrenceTargetData
                (levelFourOccurrenceTargetData top betaThree (order i) (sigma i) (horder i)
                  (root i) (region i) (parent i) (hvalid i) (hboundary i)) k))
            reference logicalLeg).card ≤
        (cwRecursiveExactTargetFiberParts
          (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
          (RecursiveOccurrenceTargetData.toCompatibilityTargets
            (cwProportionalRecursiveOccurrenceTargetData
              (levelFourOccurrenceTargetData top betaThree (order i) (sigma i) (horder i)
                (root i) (region i) (parent i) (hvalid i) (hboundary i)) k))
          reference logicalLeg).card
  have hnode : ∀ i, ∃ cutoff : ℕ, ∀ k, cutoff ≤ k → P i k := by
    intro i
    by_cases hparent : 0 < levelFourParentSamples top (root i) (region i) (parent i)
    · obtain ⟨cutoff, hcutoff⟩ :=
        eventually_budget_mul_card_levelFourOccurrenceInputProfileHoles_le_exactTarget
          top betaThree (order i) (sigma i) (horder i) (root i) (region i) (parent i)
          (hvalid i) (hboundary i) hparent hepsilon budget
      exact ⟨cutoff, fun k hkCutoff _hparent n hk hsamples reference hreference logicalLeg ↦
        hcutoff k n hkCutoff hk hsamples reference hreference logicalLeg⟩
    · exact ⟨0, fun _k _hk hparent' ↦ (hparent hparent').elim⟩
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_uniform_natCutoff_of_finite (P := P) hnode
  exact ⟨cutoff, fun i hparent k n hkCutoff hk hsamples reference hreference logicalLeg ↦
    hcutoff k hkCutoff i hparent n hk hsamples reference hreference logicalLeg⟩

end AlgebraicComplexity.Examples
