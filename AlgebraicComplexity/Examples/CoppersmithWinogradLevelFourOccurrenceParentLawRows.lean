/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceParentLawGeometry
import AlgebraicComplexity.Probability.ComplementaryProductProjectionParentLaw

set_option autoImplicit false

/-!
# Exact pooled level-four occurrence rows

The two labelled occurrence rows of a valid level-four slot pool to the normalized complete-split
law of that child.  These certificate-specific identities use only exact finite counts, the
canonical complement involution, and positive sample sizes.

They assume no compatibility estimate, cleanup, hole repair, tensor restriction, generated
certificate fact, or asymptotic statement.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- The exact identity-state pooled row is a scalar multiple of the intrinsic left-child row.
The scalar is the sum of the two ordered-slot masses, so a self-complementary slot still contains
two labelled contributions. -/
theorem levelFourOccurrenceCellJointProfile_id
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (k : ℕ) (slot : LevelFourValidSlot parent) (word : SplitWord 2) :
    (cwProportionalOccurrenceLaw
        (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) k).cellJointProfile
        (levelFourComplementSlotPerm parent) id (slot, word) =
      (levelFourSlotNumerator top root region parent slot +
          levelFourSlotNumerator top root region parent
            (levelFourComplementSlot parent slot)) *
        levelFourChildSamples *
          levelFourLeftChildWordCount betaThree region parent sigma slot c word * k := by
  classical
  rw [← recursiveComplementaryOccurrencePooledProfile_eq_cellJointProfile,
    recursiveComplementaryOccurrencePooledProfile_id]
  simp only [cwProportionalOccurrenceLaw_count,
    levelFourComplementSlotPerm_symm, levelFourComplementSlotPerm_apply,
    levelFourOccurrenceLaw_count_left, levelFourOccurrenceLaw_count_complement_right]
  ring

/-- Exact mass of one identity-state pooled child row after proportional repetition. -/
theorem levelFourOccurrenceChildMass
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (k : ℕ)
    (slot : LevelFourValidSlot parent) :
    ComplementaryOccurrenceLaw.childOccurrenceMass
        (WordType.proportionalCounts
          (levelFourOccurrenceSourceProfile top root region parent) k)
        (levelFourComplementSlotPerm parent) slot =
      (levelFourSlotNumerator top root region parent slot +
          levelFourSlotNumerator top root region parent
            (levelFourComplementSlot parent slot)) *
        (levelFourChildSamples * levelFourChildSamples) * k := by
  simp only [ComplementaryOccurrenceLaw.childOccurrenceMass,
    WordType.proportionalCounts, levelFourOccurrenceSourceProfile,
    levelFourComplementSlotPerm_symm, levelFourComplementSlotPerm_apply]
  ring

/-- Every positive pooled row normalizes to the certificate's intrinsic left-child split law. -/
theorem levelFourNormalizedChildLaw_weight
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (k : ℕ) (hk : 0 < k)
    (slot : LevelFourValidSlot parent)
    (hslot : 0 < levelFourSlotNumerator top root region parent slot +
      levelFourSlotNumerator top root region parent (levelFourComplementSlot parent slot))
    (word : SplitWord 2) :
    (ComplementaryOccurrenceLaw.normalizedChildLaw
        (cwProportionalOccurrenceLaw
          (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) k)
        (levelFourComplementSlotPerm parent) slot).weight word =
      (levelFourLeftChildWordCount betaThree region parent sigma slot c word : ℝ) /
        levelFourChildSamples := by
  have hchild : 0 < levelFourChildSamples := by
    simp [levelFourChildSamples]
  apply ComplementaryOccurrenceLaw.normalizedChildLaw_weight_of_scaled_row
    (cwProportionalOccurrenceLaw
      (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) k)
    (levelFourComplementSlotPerm parent) slot word
    (levelFourSlotNumerator top root region parent slot +
      levelFourSlotNumerator top root region parent (levelFourComplementSlot parent slot))
    levelFourChildSamples
    (levelFourLeftChildWordCount betaThree region parent sigma slot c word) k
    hslot hchild hk
  · exact levelFourOccurrenceCellJointProfile_id
      top betaThree root region parent sigma hvalid c k slot word
  · exact levelFourOccurrenceChildMass top root region parent k slot

end AlgebraicComplexity.Examples
