/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceParentLawIdentity
import AlgebraicComplexity.Probability.ComplementaryOccurrenceCellProjectionInjective

set_option autoImplicit false

/-!
# Transporting the exact level-four parent law to bounded cells

Injectivity of the bounded occurrence cell transports the identity-state parent law to the
certificate-facing finite model.

The proof assumes no compatibility estimate, cleanup, hole repair, tensor restriction, generated
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

/-- The actual bounded-cell occurrence model has the same parent law as the identity-state model.
This is the certificate-facing form of the exact parent recursion identity. -/
theorem levelFourOccurrenceProjectionModel_parentLaw
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (c : Leg) (hparent : 0 < levelFourParentSamples top root region parent)
    (k : ℕ) (hk : 0 < k) :
    let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
    let law := cwProportionalOccurrenceLaw
      (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) k
    let hmass := cwProportionalProfileMass_pos sourceProfile (by
      rw [profileMass_levelFourOccurrenceSourceProfile]
      exact hparent) k hk
    let M := law.toCellProductProjectionModel (levelFourComplementSlotPerm parent)
      (cwRecursiveOccurrenceStateCell 2
        (levelFourOccurrenceCoarseIndex parent sigma)
        (levelFourOccurrenceCoarseIndex_total parent sigma)) hmass
    M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2) =
      (((levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k).toSemantic
        (by
          rw [levelFourOccurrenceParentTerm_multiplicity]
          exact Nat.mul_pos hparent hk)).split c).probability := by
  simp only
  let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
  have hsource : 0 < WordType.profileMass sourceProfile := by
    change 0 < WordType.profileMass
      (levelFourOccurrenceSourceProfile top root region parent)
    rw [profileMass_levelFourOccurrenceSourceProfile]
    exact hparent
  let law := cwProportionalOccurrenceLaw
    (levelFourOccurrenceLaw top betaThree root region parent sigma hvalid c) k
  let hmass := cwProportionalProfileMass_pos sourceProfile hsource k hk
  let cellOf := cwRecursiveOccurrenceStateCell 2
    (levelFourOccurrenceCoarseIndex parent sigma)
    (levelFourOccurrenceCoarseIndex_total parent sigma)
  let join : SplitWord 2 × SplitWord 2 → SplitWord 3 :=
    fun pair ↦ concatSplitWords pair.1 pair.2
  calc
    _ = (law.toComplementaryProductProjectionModel
        (levelFourComplementSlotPerm parent) hmass).parentLaw join := by
      exact law.toCellProductProjectionModel_parentLaw_eq_identity_of_injective
        (levelFourComplementSlotPerm parent) cellOf
        (levelFourOccurrenceStateCell_injective parent sigma) hmass join
    _ = _ := by
      change
        (levelFourOccurrenceIdentityModel
          top betaThree root region parent sigma hvalid c hparent k hk).parentLaw
            (fun pair ↦ concatSplitWords pair.1 pair.2) = _
      exact levelFourOccurrenceIdentityModel_parentLaw
        top betaThree root region parent sigma hvalid c hparent k hk

end AlgebraicComplexity.Examples
