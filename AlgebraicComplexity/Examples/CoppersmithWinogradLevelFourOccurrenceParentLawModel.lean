/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceSource
import AlgebraicComplexity.Probability.ComplementaryOccurrenceProjection
import AlgebraicComplexity.Probability.IntegralProfileProbabilityScaling

set_option autoImplicit false

/-!
# Exact level-four occurrence state model

This file defines the identity-state complementary-product model and proves its exact outer-state
normalization.  It also records the elementary active-slot sum identity and the child-product
sample scale.  Later files can therefore reason about the model without unfolding certificate
counts into one large kernel term.
-/

open scoped BigOperators

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

private theorem cancel_common_right_nat
    (a b common : ℕ) (hcommon : 0 < common) :
    (((a * common : ℕ) : ℝ) / ((b * common : ℕ) : ℝ)) =
      (a : ℝ) / b := by
  simp only [Nat.cast_mul]
  apply mul_div_mul_right
  exact_mod_cast hcommon.ne'

@[simp] theorem levelFourChildProductScale_eq_childSamples_sq :
    levelFourChildProductScale = levelFourChildSamples * levelFourChildSamples := by
  simp [levelFourChildProductScale, levelFourChildSamples, two_mul, pow_add]

/-- Multiplying the top-split numerator by an arbitrary slot statistic is unaffected by removing
the structurally zero slots. -/
theorem sum_levelFourActiveSlot_numerator_mul
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount)
    (f : LevelFourValidSlot parent → ℕ) :
    (∑ slot : LevelFourActiveSlot top root region parent,
        levelFourSlotNumerator top root region parent slot.1 * f slot.1) =
      ∑ slot : LevelFourValidSlot parent,
        levelFourSlotNumerator top root region parent slot * f slot := by
  calc
    (∑ slot : LevelFourActiveSlot top root region parent,
        levelFourSlotNumerator top root region parent slot.1 * f slot.1) =
        ∑ slot ∈ levelFourActiveSlots top root region parent,
          levelFourSlotNumerator top root region parent slot * f slot :=
      (Finset.sum_subtype (levelFourActiveSlots top root region parent)
        (fun _ ↦ Iff.rfl)
        (fun slot ↦ levelFourSlotNumerator top root region parent slot * f slot)).symm
    _ = ∑ slot : LevelFourValidSlot parent,
        levelFourSlotNumerator top root region parent slot * f slot := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro slot _ hnot
      have hzero : levelFourSlotNumerator top root region parent slot = 0 := by
        simpa [levelFourActiveSlots] using hnot
      simp [hzero]

/-- Identity-state normalization of the repeated labelled-occurrence package. -/
noncomputable def levelFourOccurrenceIdentityModel
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (hparent : 0 < levelFourParentSamples top root region parent)
    (k : ℕ) (hk : 0 < k) :
    ComplementaryProductProjectionModel
      (LevelFourValidSlot parent) (LevelFourValidSlot parent) (SplitWord 2) :=
  ComplementaryOccurrenceLaw.toComplementaryProductProjectionModel
    (cwProportionalOccurrenceLaw
      (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) k)
    (levelFourComplementSlotPerm parent)
      (cwProportionalProfileMass_pos
        (levelFourOccurrenceSourceProfile top root region parent)
        (by
          rw [profileMass_levelFourOccurrenceSourceProfile]
          exact hparent)
        k hk)

@[simp] theorem levelFourOccurrenceIdentityModel_stateLaw_weight
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (hparent : 0 < levelFourParentSamples top root region parent)
    (k : ℕ) (hk : 0 < k) (slot : LevelFourValidSlot parent) :
    (levelFourOccurrenceIdentityModel top betaThree root region parent sigma hvalid c
      hparent k hk).stateLaw.weight slot =
      (levelFourSlotNumerator top root region parent slot : ℝ) /
        levelFourSamples top root region parent := by
  have hsourceMass :
      0 < WordType.profileMass
        (levelFourOccurrenceSourceProfile top root region parent) := by
    rw [profileMass_levelFourOccurrenceSourceProfile]
    exact hparent
  have hscaledMass :
      0 < WordType.profileMass
        (WordType.proportionalCounts
          (levelFourOccurrenceSourceProfile top root region parent) k) :=
    cwProportionalProfileMass_pos
      (levelFourOccurrenceSourceProfile top root region parent) hsourceMass k hk
  change
    (WordType.normalizedProfileProbability
      (WordType.proportionalCounts
        (levelFourOccurrenceSourceProfile top root region parent) k) hscaledMass).weight slot = _
  rw [WordType.normalizedProfileProbability_proportionalCounts_weight
    (levelFourOccurrenceSourceProfile top root region parent) hsourceMass k hk slot]
  simp only [profileMass_levelFourOccurrenceSourceProfile, levelFourOccurrenceSourceProfile,
    levelFourParentSamples, levelFourChildProductScale_eq_childSamples_sq]
  have hcommon : 0 < levelFourChildSamples * levelFourChildSamples := by
    simp [levelFourChildSamples]
  exact cancel_common_right_nat _ _ _ hcommon

@[simp] theorem levelFourOccurrenceIdentityModel_childLaw
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (hparent : 0 < levelFourParentSamples top root region parent)
    (k : ℕ) (hk : 0 < k) (slot : LevelFourValidSlot parent) :
    (levelFourOccurrenceIdentityModel top betaThree root region parent sigma hvalid c
      hparent k hk).childLaw slot =
      ComplementaryOccurrenceLaw.normalizedChildLaw
        (cwProportionalOccurrenceLaw
          (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) k)
        (levelFourComplementSlotPerm parent) slot :=
  rfl

end AlgebraicComplexity.Examples
