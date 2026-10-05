/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceParentLaw

set_option autoImplicit false

/-!
# Level-four occurrence concentration

This file connects the exact level-four occurrence parent law to the generic recursive
concentration model.  Its first bridge identifies the projection model built from the semantic
compatibility-target package with the certificate-independent model whose parent law was computed
exactly.

No compatible-family cardinality, cleanup, repair, tensor restriction, generated certificate
fact, or asymptotic estimate is assumed here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- The projection model constructed from the exact level-four target package has the recursively
assembled parent complete-split law.  This is the `hparentReference` premise expected by the
generic occurrence-concentration theorem, proved from finite occurrence counts rather than passed
through as a client hypothesis. -/
theorem levelFourOccurrenceTargetData_parentLaw
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val)
    (c : Leg) (hparent : 0 < levelFourParentSamples top root region parent)
    (k : ℕ) (hk : 0 < k) :
    let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
    let data := cwProportionalRecursiveOccurrenceTargetData
      (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
        hvalid hboundary) k
    let hmass := cwProportionalProfileMass_pos sourceProfile (by
      rw [profileMass_levelFourOccurrenceSourceProfile]
      exact hparent) k hk
    let M := cwRecursiveOccurrenceProjectionModel
      (levelFourOccurrenceCoarseIndex parent sigma) data c
        (levelFourComplementSlotPerm parent)
        (levelFourOccurrenceCoarseIndex_total parent sigma) hmass
    M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2) =
      (((levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k).toSemantic
        (by
          rw [levelFourOccurrenceParentTerm_multiplicity]
          exact Nat.mul_pos hparent hk)).split c).probability := by
  dsimp only
  change
    (ComplementaryOccurrenceLaw.toCellProductProjectionModel
        (cwProportionalOccurrenceLaw
          (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) k)
        (levelFourComplementSlotPerm parent)
        (cwRecursiveOccurrenceStateCell 2
          (levelFourOccurrenceCoarseIndex parent sigma)
          (levelFourOccurrenceCoarseIndex_total parent sigma)) _).parentLaw
        (fun pair ↦ concatSplitWords pair.1 pair.2) = _
  exact levelFourOccurrenceProjectionModel_parentLaw
    top betaThree root region parent sigma hvalid c hparent k hk

end AlgebraicComplexity.Examples
