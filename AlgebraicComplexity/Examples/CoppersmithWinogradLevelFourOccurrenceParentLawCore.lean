/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceParentLawLeft

set_option autoImplicit false

/-!
# The exact right-child law of the level-four identity model

Applying pooled-row normalization at the complementary ordered slot and using the complement
involution gives the right-child law.  The left-child law lives in the preceding small checkpoint.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- A positive ordered state exposes its intrinsic right-child split law through the complementary
state of the identity projection model. -/
theorem levelFourOccurrenceIdentityModel_rightChildLaw_weight_of_ne
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
        top betaThree root region parent sigma hvalid c hparent k hk).cellOf
        ((levelFourOccurrenceIdentityModel
          top betaThree root region parent sigma hvalid c hparent k hk).complement slot))).weight
      word =
      (levelFourRightChildWordCount betaThree region parent sigma slot c word : ℝ) /
        levelFourChildSamples := by
  rw [show
    (levelFourOccurrenceIdentityModel
      top betaThree root region parent sigma hvalid c hparent k hk).cellOf
        ((levelFourOccurrenceIdentityModel
          top betaThree root region parent sigma hvalid c hparent k hk).complement slot) =
      levelFourComplementSlot parent slot by rfl]
  rw [levelFourOccurrenceIdentityModel_childLaw]
  have hslot :
      0 < levelFourSlotNumerator top root region parent slot +
        levelFourSlotNumerator top root region parent
          (levelFourComplementSlot parent slot) :=
    Nat.add_pos_left (Nat.pos_of_ne_zero hnum) _
  have hcomplement :
      0 < levelFourSlotNumerator top root region parent
          (levelFourComplementSlot parent slot) +
        levelFourSlotNumerator top root region parent
          (levelFourComplementSlot parent (levelFourComplementSlot parent slot)) := by
    rw [levelFourComplementSlot_involutive parent slot, Nat.add_comm]
    exact hslot
  rw [levelFourNormalizedChildLaw_weight
    top betaThree root region parent sigma hvalid c k hk
      (levelFourComplementSlot parent slot) hcomplement word]
  rw [levelFourRightChildWordCount_eq_left_complementSlot]

end AlgebraicComplexity.Examples
