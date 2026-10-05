/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceExactTargetCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceInputHoleGrowth

set_option autoImplicit false

/-!
# Exact target growth for level-four occurrence input holes

This module combines the exact fixed-node conditional-type lower bound with the level-four
input-hole tail estimate.  For every fixed valid node and fixed repair budget, the actual recursive
target fiber eventually absorbs all input-profile holes, uniformly over marked references and the
three logical legs.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- **Repair-ready level-four input-hole bound with the actual target.**  For a fixed valid node
and positive tolerance, every fixed repair budget is eventually absorbed by the exact recursive
target fiber, uniformly in marked references and logical legs. -/
theorem eventually_budget_mul_card_levelFourOccurrenceInputProfileHoles_le_exactTarget
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val)
    (hparent : 0 < levelFourParentSamples top root region parent)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (budget : ℕ) :
    ∃ cutoff : ℕ, ∀ k n : ℕ, cutoff ≤ k → ∀ _hk : 0 < k,
      ∀ (hsamples :
        WordType.profileMass
          (levelFourOccurrenceSourceProfile top root region parent) * k = n + 1)
        (reference : CWRecursiveCoarseAddress 2 n),
      reference ∈
          cwRecursiveRelaxedMarkedCoarseSupport
            (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
            (Equiv.refl Leg)
            (levelFourOccurrenceSplitType top betaThree root region parent sigma hvalid k n
              hsamples) →
      ∀ logicalLeg : Leg,
        budget *
            (cwRecursiveInputProfileHoles
              (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
              (levelFourOccurrenceParentTerm
                top betaThree root region parent sigma hvalid k)
              (levelFourOccurrenceParentTerm_multiplicity_eq_succ
                top betaThree root region parent sigma hvalid k n hsamples)
              epsilon
              (RecursiveOccurrenceTargetData.toCompatibilityTargets
                (cwProportionalRecursiveOccurrenceTargetData
                (levelFourOccurrenceTargetData
                  top betaThree order sigma horder root region parent hvalid hboundary) k))
              reference logicalLeg).card ≤
          (cwRecursiveExactTargetFiberParts
            (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
            (RecursiveOccurrenceTargetData.toCompatibilityTargets
              (cwProportionalRecursiveOccurrenceTargetData
              (levelFourOccurrenceTargetData
                top betaThree order sigma horder root region parent hvalid hboundary) k))
            reference logicalLeg).card := by
  let targetLoss : ℕ → ℝ := fun k ↦
    levelFourOccurrenceExactTargetLoss
        top betaThree root region parent sigma hvalid .X k +
      levelFourOccurrenceExactTargetLoss
        top betaThree root region parent sigma hvalid .Y k +
      levelFourOccurrenceExactTargetLoss
        top betaThree root region parent sigma hvalid .Z k
  have htargetLoss : Growth.Subexponential targetLoss := by
    exact
      ((levelFourOccurrenceExactTargetLoss_subexponential
          top betaThree root region parent sigma hvalid .X).add
        (levelFourOccurrenceExactTargetLoss_subexponential
          top betaThree root region parent sigma hvalid .Y)).add
        (levelFourOccurrenceExactTargetLoss_subexponential
          top betaThree root region parent sigma hvalid .Z)
  obtain ⟨cutoff, hcutoff⟩ :=
    eventually_budget_mul_card_levelFourOccurrenceInputProfileHoles_le_of_targetGrowth
      top betaThree order sigma horder root region parent hvalid hboundary hparent
        hepsilon targetLoss htargetLoss budget
  refine ⟨cutoff, ?_⟩
  intro k n hkCutoff _hk hsamples reference hreference logicalLeg
  apply hcutoff k n hkCutoff _hk hsamples reference hreference logicalLeg
  calc
      Real.exp ((k : ℝ) *
          ((WordType.profileMass
              (levelFourOccurrenceSourceProfile top root region parent) : ℝ) *
            (cwRecursiveOccurrenceProjectionModel
              (levelFourOccurrenceCoarseIndex parent sigma)
              (cwProportionalRecursiveOccurrenceTargetData
                (levelFourOccurrenceTargetData
                  top betaThree order sigma horder root region parent hvalid hboundary) k)
              logicalLeg (levelFourComplementSlotPerm parent)
              (levelFourOccurrenceCoarseIndex_total parent sigma)
              (cwProportionalProfileMass_pos
                (levelFourOccurrenceSourceProfile top root region parent) (by
                  rw [profileMass_levelFourOccurrenceSourceProfile]
                  exact hparent) k _hk)).reference.conditionalEntropy
                (cwRecursiveOccurrenceProjectionModel
                  (levelFourOccurrenceCoarseIndex parent sigma)
                  (cwProportionalRecursiveOccurrenceTargetData
                    (levelFourOccurrenceTargetData
                      top betaThree order sigma horder root region parent hvalid hboundary) k)
                  logicalLeg (levelFourComplementSlotPerm parent)
                  (levelFourOccurrenceCoarseIndex_total parent sigma)
                  (cwProportionalProfileMass_pos
                    (levelFourOccurrenceSourceProfile top root region parent) (by
                      rw [profileMass_levelFourOccurrenceSourceProfile]
                      exact hparent) k _hk)).coarse)) ≤
          levelFourOccurrenceExactTargetLoss
              top betaThree root region parent sigma hvalid logicalLeg k *
            ((cwRecursiveExactTargetFiberParts
              (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
              (RecursiveOccurrenceTargetData.toCompatibilityTargets
                (cwProportionalRecursiveOccurrenceTargetData
                (levelFourOccurrenceTargetData
                  top betaThree order sigma horder root region parent hvalid hboundary) k))
              reference logicalLeg).card : ℝ) :=
        exp_referenceConditionalEntropy_le_exactTargetLoss_mul_card
          top betaThree order sigma horder root region parent hvalid hboundary
            k n _hk hparent hsamples reference hreference logicalLeg
      _ ≤ targetLoss k *
          ((cwRecursiveExactTargetFiberParts
            (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
            (RecursiveOccurrenceTargetData.toCompatibilityTargets
              (cwProportionalRecursiveOccurrenceTargetData
              (levelFourOccurrenceTargetData
                top betaThree order sigma horder root region parent hvalid hboundary) k))
            reference logicalLeg).card : ℝ) := by
        have hX := levelFourOccurrenceExactTargetLoss_pos
          top betaThree root region parent sigma hvalid .X k
        have hY := levelFourOccurrenceExactTargetLoss_pos
          top betaThree root region parent sigma hvalid .Y k
        have hZ := levelFourOccurrenceExactTargetLoss_pos
          top betaThree root region parent sigma hvalid .Z k
        exact mul_le_mul_of_nonneg_right
          (by
            cases logicalLeg <;> dsimp only [targetLoss] <;> linarith)
          (by positivity)

end AlgebraicComplexity.Examples
