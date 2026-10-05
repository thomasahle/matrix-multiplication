/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceParentLawRows

set_option autoImplicit false

/-!
# The exact left-child law of the level-four identity model

The pooled-row normalization theorem gives the left-child law directly.  This small checkpoint
keeps the concrete reduction independent of the complementary right-child calculation.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- A positive ordered state exposes its intrinsic left-child split law through the identity
projection model. -/
theorem levelFourOccurrenceIdentityModel_leftChildLaw_weight_of_ne
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (hparent : 0 < levelFourParentSamples top root region parent)
    (k : ℕ) (hk : 0 < k) (slot : LevelFourValidSlot parent)
    (word : SplitWord 2)
    (hnum : levelFourSlotNumerator top root region parent slot ≠ 0) :
    ((levelFourOccurrenceIdentityModel
        top betaThree root region parent sigma hvalid c hparent k hk).childLaw
      ((levelFourOccurrenceIdentityModel
        top betaThree root region parent sigma hvalid c hparent k hk).cellOf slot)).weight word =
      (levelFourLeftChildWordCount betaThree region parent sigma slot c word : ℝ) /
        levelFourChildSamples := by
  rw [show
    (levelFourOccurrenceIdentityModel
      top betaThree root region parent sigma hvalid c hparent k hk).cellOf slot = slot by rfl]
  rw [levelFourOccurrenceIdentityModel_childLaw]
  exact levelFourNormalizedChildLaw_weight
    top betaThree root region parent sigma hvalid c k hk slot
      (Nat.add_pos_left (Nat.pos_of_ne_zero hnum) _) word

end AlgebraicComplexity.Examples
