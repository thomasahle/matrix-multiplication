/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceConcentration
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightRecursiveOccurrenceClients

set_option autoImplicit false

/-!
# The finite level-four occurrence input-hole bound

This file instantiates the generic recursive occurrence-concentration theorem with the exact
level-four certificate semantics.  A marked quotient reference supplies its ordered valid-slot
word; the occurrence package supplies the exact child tables; and the finite parent-law theorem
identifies their joined law with the recursively assembled complete-split profile.

The theorem introduces no compatibility-count, cleanup, repair, tensor-restriction, generated
certificate, or asymptotic hypothesis.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- The proportional level-four parent term has exactly the sample count used by its marked
recursive split type. -/
theorem levelFourOccurrenceParentTerm_multiplicity_eq_succ
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (sigma : Orientation)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (k n : ℕ)
    (hsamples :
      WordType.profileMass (levelFourOccurrenceSourceProfile top root region parent) * k = n + 1) :
    (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k).multiplicity =
      n + 1 := by
  rw [levelFourOccurrenceParentTerm_multiplicity,
    ← profileMass_levelFourOccurrenceSourceProfile]
  exact hsamples

/-- **Certificate-facing finite input-hole bound.**  Every marked level-four quotient reference
has at most the generic conditional-type tail of children rejected by the approximate parent
profile selector.  All semantic premises of the generic theorem are constructed here from the
exact occurrence tables. -/
theorem card_levelFourOccurrenceInputProfileHoles_le
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val)
    (k n : ℕ) (hk : 0 < k)
    (hparent : 0 < levelFourParentSamples top root region parent)
    (hsamples :
      WordType.profileMass (levelFourOccurrenceSourceProfile top root region parent) * k = n + 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (reference : CWRecursiveCoarseAddress 2 n)
    (hreference : reference ∈
      cwRecursiveRelaxedMarkedCoarseSupport
        (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
        (Equiv.refl Leg)
        (levelFourOccurrenceSplitType top betaThree root region parent sigma hvalid k n
          hsamples))
    (logicalLeg : Leg) :
    let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
    let scaledData := cwProportionalRecursiveOccurrenceTargetData
      (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
        hvalid hboundary) k
    let hmass := cwProportionalProfileMass_pos sourceProfile (by
      rw [profileMass_levelFourOccurrenceSourceProfile]
      exact hparent) k hk
    let M := cwRecursiveOccurrenceProjectionModel
      (levelFourOccurrenceCoarseIndex parent sigma) scaledData logicalLeg
        (levelFourComplementSlotPerm parent)
        (levelFourOccurrenceCoarseIndex_total parent sigma) hmass
    ((cwRecursiveInputProfileHoles
        (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
        (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
        (levelFourOccurrenceParentTerm_multiplicity_eq_succ
          top betaThree root region parent sigma hvalid k n hsamples)
        epsilon scaledData.toCompatibilityTargets reference logicalLeg).card : ℝ) ≤
      ((((WordType.profileMass sourceProfile * k + 1) ^
          Fintype.card
            (LevelFourValidSlot parent × (SplitWord 2 × SplitWord 2)) : ℕ) : ℝ)) *
        WordType.structuralZeroMultinomialLoss sourceProfile k *
          Real.exp (((k : ℝ) * WordType.profileMass sourceProfile) *
            (M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4)) := by
  let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
  have hsourceMass : 0 < WordType.profileMass sourceProfile := by
    change 0 < WordType.profileMass
      (levelFourOccurrenceSourceProfile top root region parent)
    rw [profileMass_levelFourOccurrenceSourceProfile]
    exact hparent
  let term := levelFourOccurrenceParentTerm
    top betaThree root region parent sigma hvalid k
  have hmultiplicity : term.multiplicity = n + 1 := by
    exact levelFourOccurrenceParentTerm_multiplicity_eq_succ
      top betaThree root region parent sigma hvalid k n hsamples
  let alpha := levelFourOccurrenceSplitType
    top betaThree root region parent sigma hvalid k n hsamples
  let baseData := levelFourOccurrenceTargetData
    top betaThree order sigma horder root region parent hvalid hboundary
  let scaledData := cwProportionalRecursiveOccurrenceTargetData baseData k
  let hmass := cwProportionalProfileMass_pos sourceProfile hsourceMass k hk
  let coarseOf := levelFourOccurrenceCoarseIndex parent sigma
  let complement := levelFourComplementSlotPerm parent
  let M := cwRecursiveOccurrenceProjectionModel coarseOf scaledData logicalLeg complement
    (levelFourOccurrenceCoarseIndex_total parent sigma) hmass
  have hscaledSupported : ∀ c occurrence word,
      (scaledData.law c).count occurrence word ≠ 0 →
        splitWordWeight word = (coarseOf occurrence).get c := by
    intro c occurrence word hcount
    apply cwTotalWeightLevelFourOccurrenceLaw_supported
      top betaThree root region parent sigma hvalid c occurrence word
    intro hzero
    exact hcount (by
      simp [scaledData, baseData, levelFourOccurrenceTargetData, hzero])
  have hsupported : scaledData.toCompatibilityTargets.IsWeightSupported :=
    cwRecursiveOccurrenceTargetData_isWeightSupported coarseOf scaledData hscaledSupported
  have hcoarseSupported :
      CWRecursiveTargetCoarseTotalSupported scaledData.toCompatibilityTargets :=
    recursiveOccurrenceTargetData_toCompatibilityTargets_isCoarseTotalSupported
      scaledData (levelFourOccurrenceCoarseIndex_total parent sigma)
  have hcoarse : ∀ occurrence,
      coarseOf occurrence = coarseOf (occurrence.childState complement, .left) := by
    intro occurrence
    calc
      coarseOf occurrence = levelFourSlotCoarseIndex parent sigma
          (occurrence.childState complement) :=
        levelFourOccurrenceCoarseIndex_eq_childState parent sigma occurrence
      _ = coarseOf (occurrence.childState complement, .left) := rfl
  have hambient : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term (Equiv.refl Leg) alpha :=
    cwRecursiveRelaxedMarkedCoarseSupport_subset_ambient term (Equiv.refl Leg) alpha hreference
  obtain ⟨state, hsource, hsourceCells⟩ :=
    exists_levelFourOccurrenceStateWord_of_markedReference
      top betaThree root region parent sigma hvalid k n hsamples reference hreference
  have hparentReference :
      M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2) =
        ((cwRecursiveSemanticParentTerm term hmultiplicity).split logicalLeg).probability := by
    change
      (cwRecursiveOccurrenceProjectionModel
          (levelFourOccurrenceCoarseIndex parent sigma) scaledData logicalLeg
          (levelFourComplementSlotPerm parent)
          (levelFourOccurrenceCoarseIndex_total parent sigma) hmass).parentLaw
          (fun pair ↦ concatSplitWords pair.1 pair.2) =
        ((term.toSemantic _).split logicalLeg).probability
    exact levelFourOccurrenceTargetData_parentLaw
      top betaThree order sigma horder root region parent hvalid hboundary logicalLeg
        hparent k hk
  have hbound := card_cwRecursiveInputProfileHoles_le_of_occurrenceTargetData
    (fun _ ↦ PUnit.unit) (Equiv.refl Leg) term
      (levelFourOccurrenceParentTerm_multiplicity_eq_succ
        top betaThree root region parent sigma hvalid k n hsamples)
      hepsilon alpha
      sourceProfile hsourceMass k hk coarseOf scaledData complement
      (levelFourOccurrenceCoarseIndex_total parent sigma) hcoarse hsupported
      hcoarseSupported reference hambient logicalLeg state hsource hsourceCells hparentReference
  convert hbound using 1
  simp only [sourceProfile, baseData, scaledData, coarseOf, complement, term,
    Equiv.refl_apply]
  rfl

end AlgebraicComplexity.Examples
