/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceParentLawCore

set_option autoImplicit false

/-!
# The exact level-four identity-state parent law

Mixing the exact normalized child-occurrence rows with the ordered top-split law recovers the
recursively assembled parent complete-split distribution.  This checkpoint contains only that
finite mixture calculation.

The proof assumes no compatibility estimate, cleanup, hole repair, tensor restriction, generated
certificate fact, or asymptotic statement.
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

/-- Concatenating the two normalized occurrence rows and mixing by the ordered top-split law is
exactly the recursively assembled parent complete-split distribution. -/
theorem levelFourOccurrenceIdentityModel_parentLaw
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (hparent : 0 < levelFourParentSamples top root region parent)
    (k : ℕ) (hk : 0 < k) :
    let M := levelFourOccurrenceIdentityModel
      top betaThree root region parent sigma hvalid c hparent k hk
    M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2) =
      (((levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k).toSemantic
        (by
          rw [levelFourOccurrenceParentTerm_multiplicity]
          exact Nat.mul_pos hparent hk)).split c).probability := by
  dsimp only
  let baseTerm := levelFourRecursiveParentTerm
    top betaThree root region parent sigma hvalid
  have hbase : 0 < baseTerm.multiplicity := by
    simpa only [baseTerm, levelFourRecursiveParentTerm_multiplicity] using hparent
  have hscaled :
      0 < (levelFourOccurrenceParentTerm
        top betaThree root region parent sigma hvalid k).multiplicity := by
    rw [levelFourOccurrenceParentTerm_multiplicity]
    exact Nat.mul_pos hparent hk
  have hscale :
      ((((levelFourOccurrenceParentTerm
        top betaThree root region parent sigma hvalid k).toSemantic hscaled).split c).probability) =
        ((baseTerm.toSemantic hbase).split c).probability := by
    change (((baseTerm.scale k).toSemantic _).split c).probability =
      ((baseTerm.toSemantic hbase).split c).probability
    exact congrArg (fun split ↦ split.probability)
      (ExactInterfaceTermParameters.scale_toSemantic_split baseTerm hbase k hk c)
  rw [hscale]
  apply ProbabilityVector.ext
  funext word
  rw [ComplementaryProductProjectionModel.parentLaw_concatSplitWords_weight_eq_normalizedCounts
    (levelFourOccurrenceIdentityModel
      top betaThree root region parent sigma hvalid c hparent k hk)
    (levelFourSlotNumerator top root region parent)
    (levelFourLeftChildWordCount betaThree region parent sigma · c ·)
    (levelFourRightChildWordCount betaThree region parent sigma · c ·)
    (levelFourSamples top root region parent)
    levelFourChildSamples
    (levelFourParentSamples top root region parent)
    (levelFourOccurrenceIdentityModel_stateLaw_weight
      top betaThree root region parent sigma hvalid c hparent k hk)
    (levelFourOccurrenceIdentityModel_leftChildLaw_weight_of_ne
      top betaThree root region parent sigma hvalid c hparent k hk)
    (levelFourOccurrenceIdentityModel_rightChildLaw_weight_of_ne
      top betaThree root region parent sigma hvalid c hparent k hk)
    (by
      simp only [levelFourParentSamples,
        levelFourChildProductScale_eq_childSamples_sq])
    word]
  change _ = ((baseTerm.split c).toDistribution hbase).weight word
  rw [CompleteSplitProfile.toDistribution_weight]
  simp only [baseTerm, levelFourRecursiveParentTerm_split_counts,
    levelFourRecursiveParentTerm_multiplicity]
  let slotProduct : LevelFourValidSlot parent → ℕ := fun slot ↦
    levelFourLeftChildWordCount betaThree region parent sigma slot c
        (splitWordSuccEquiv 2 word).1 *
      levelFourRightChildWordCount betaThree region parent sigma slot c
        (splitWordSuccEquiv 2 word).2
  have hsum :
      (∑ slot : LevelFourValidSlot parent,
          levelFourSlotNumerator top root region parent slot * slotProduct slot) =
        levelFourSemanticParentWordCount
          top betaThree root region parent sigma c word := by
    rw [levelFourSemanticParentWordCount]
    exact (sum_levelFourActiveSlot_numerator_mul
      top root region parent slotProduct).symm
  change
    ((∑ slot : LevelFourValidSlot parent,
      levelFourSlotNumerator top root region parent slot * slotProduct slot : ℕ) : ℝ) /
        levelFourParentSamples top root region parent =
      (levelFourSemanticParentWordCount
        top betaThree root region parent sigma c word : ℝ) /
          levelFourParentSamples top root region parent
  rw [hsum]

end AlgebraicComplexity.Examples
