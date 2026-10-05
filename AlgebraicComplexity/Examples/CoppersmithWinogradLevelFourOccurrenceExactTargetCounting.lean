/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceExactTargetProfile
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveExactTargetConditionalType
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightRecursiveOccurrenceClients

set_option autoImplicit false

/-!
# Exact target counting for level-four complementary occurrences

The exact recursive target fiber is a conditional type class.  This module identifies its
cardinality with the evaluator's multinomial product and proves that its leading base is the
conditional entropy of the complementary-product projection model, up to an explicit positive
subexponential structural-zero loss.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- **Actual exact-target lower bound.**  The exact level-four target fiber at a marked reference
has the same leading conditional entropy as the occurrence projection model, up to the explicit
positive subexponential structural-zero loss. -/
theorem exp_referenceConditionalEntropy_le_exactTargetLoss_mul_card
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
    Real.exp ((k : ℝ) *
        ((WordType.profileMass sourceProfile : ℝ) *
          M.reference.conditionalEntropy M.coarse)) ≤
      levelFourOccurrenceExactTargetLoss
          top betaThree root region parent sigma hvalid logicalLeg k *
        ((cwRecursiveExactTargetFiberParts
          (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
          scaledData.toCompatibilityTargets reference logicalLeg).card : ℝ) := by
  classical
  dsimp only
  let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
  have hsourceMass : 0 < WordType.profileMass sourceProfile := by
    change 0 < WordType.profileMass
      (levelFourOccurrenceSourceProfile top root region parent)
    rw [profileMass_levelFourOccurrenceSourceProfile]
    exact hparent
  let coarseOf := levelFourOccurrenceCoarseIndex parent sigma
  let complement := levelFourComplementSlotPerm parent
  let cellOf := cwRecursiveOccurrenceStateCell 2 coarseOf
    (levelFourOccurrenceCoarseIndex_total parent sigma)
  let law := levelFourOccurrenceLaw
    top betaThree root region parent sigma hvalid logicalLeg
  let cellProfile := levelFourOccurrenceExactTargetCellProfile
    top root region parent sigma
  let jointProfile := levelFourOccurrenceExactTargetJointProfile
    top betaThree root region parent sigma hvalid logicalLeg
  let baseData := levelFourOccurrenceTargetData
    top betaThree order sigma horder root region parent hvalid hboundary
  let scaledData := cwProportionalRecursiveOccurrenceTargetData baseData k
  let targets := scaledData.toCompatibilityTargets
  let hmass := cwProportionalProfileMass_pos sourceProfile hsourceMass k hk
  let M := cwRecursiveOccurrenceProjectionModel coarseOf scaledData logicalLeg
    complement (levelFourOccurrenceCoarseIndex_total parent sigma) hmass
  let source := cwRecursiveOrientedFiniteCellSequence
    2 n (fun _ ↦ PUnit.unit) (Equiv.refl Leg) reference
  let scaledJoint :
      CWOrientedCoarseCell PUnit.{1} 2 × SplitWord 2 → ℕ :=
    fun pair ↦ targets.exactProfile logicalLeg
      (cwOrientedCoarseCellToIndex pair.1) pair.2
  have hmargin :
      WordType.mappedType Prod.fst jointProfile = cellProfile := by
    change WordType.mappedType Prod.fst
        (law.cellJointProfile complement cellOf) =
      complementaryOccurrenceCellProfile sourceProfile complement cellOf
    exact law.mappedType_fst_cellJointProfile complement cellOf
  have hcellMass :
      0 < WordType.profileMass cellProfile := by
    rw [show cellProfile =
        complementaryOccurrenceCellProfile sourceProfile complement cellOf by rfl,
      ComplementaryOccurrenceLaw.profileMass_complementaryOccurrenceCellProfile]
    exact Nat.mul_pos (by norm_num) hsourceMass
  have hcellMassValue :
      WordType.profileMass cellProfile =
        2 * WordType.profileMass sourceProfile := by
    rw [show cellProfile =
        complementaryOccurrenceCellProfile sourceProfile complement cellOf by rfl,
      ComplementaryOccurrenceLaw.profileMass_complementaryOccurrenceCellProfile]
  have hlength :
      WordType.profileMass cellProfile * k = (n + 1) + (n + 1) := by
    rw [hcellMassValue, Nat.mul_assoc, hsamples]
    omega
  obtain ⟨state, hstate, hsourceCells⟩ :=
    exists_levelFourOccurrenceStateWord_of_markedReference
      top betaThree root region parent sigma hvalid k n hsamples reference hreference
  have hsource :
      WordType.multiplicity source =
        WordType.proportionalCounts cellProfile k := by
    rw [show source =
        Fin.append (cellOf ∘ state) (cellOf ∘ complement ∘ state) by
      exact hsourceCells]
    exact ComplementaryOccurrenceLaw.multiplicity_append_cellOf_complement
      sourceProfile complement cellOf k (n + 1) state hstate
  have hscaledJoint :
      scaledJoint = WordType.proportionalCounts jointProfile k := by
    funext pair
    exact levelFourOccurrenceScaledExactProfile_eq_proportionalJointProfile
      top betaThree order sigma horder root region parent hvalid hboundary
        logicalLeg k pair.1 pair.2
  have hscaledSupported : ∀ c occurrence word,
      (scaledData.law c).count occurrence word ≠ 0 →
        splitWordWeight word = (coarseOf occurrence).get c := by
    intro c occurrence word hcount
    apply cwTotalWeightLevelFourOccurrenceLaw_supported
      top betaThree root region parent sigma hvalid c occurrence word
    intro hzero
    exact hcount (by
      simp [scaledData, baseData, levelFourOccurrenceTargetData, hzero])
  have hsupported : targets.IsWeightSupported :=
    cwRecursiveOccurrenceTargetData_isWeightSupported coarseOf scaledData hscaledSupported
  have hcoarseSupported :
      CWRecursiveTargetCoarseTotalSupported targets :=
    recursiveOccurrenceTargetData_toCompatibilityTargets_isCoarseTotalSupported
      scaledData (levelFourOccurrenceCoarseIndex_total parent sigma)
  have hjointNative :
      scaledJoint = fun pair : CWOrientedCoarseCell PUnit.{1} 2 × SplitWord 2 ↦
        targets.exactProfile logicalLeg
          (cwOrientedCoarseCellToIndex pair.1) pair.2 := by
    rfl
  have htargetConditional :
      (cwRecursiveExactTargetFiberParts
          (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
          targets reference logicalLeg).card =
        (WordType.conditionalTypeClass source scaledJoint).card := by
    exact card_cwRecursiveExactTargetFiberParts_eq_card_conditionalTypeClass_of_joint_eq
      (Part := PUnit.{1}) (depth := 2) (n := n)
      (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
      targets hsupported hcoarseSupported reference logicalLeg
      scaledJoint hjointNative
  have hcards :
      (WordType.conditionalTypeClass source
          (WordType.proportionalCounts jointProfile k)).card =
        (cwRecursiveExactTargetFiberParts
          (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
          targets reference logicalLeg).card := by
    calc
      (WordType.conditionalTypeClass source
          (WordType.proportionalCounts jointProfile k)).card =
          (WordType.conditionalTypeClass source scaledJoint).card := by
            rw [hscaledJoint]
      _ = (cwRecursiveExactTargetFiberParts
          (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
          targets reference logicalLeg).card := htargetConditional.symm
  have hconditional :=
    WordType.conditionalProfileEntropyBase_pow_le_structuralZeroLoss_mul_card_of_length_eq
      cellProfile jointProfile hmargin hcellMass k hk hlength source hsource
  have hscaledEntropy :=
    ComplementaryOccurrenceLaw.conditionalProfileEntropyBase_cellJointProfile
      (cwProportionalOccurrenceLaw law k) complement cellOf hmass
  have hscaledCellProfile :
      complementaryOccurrenceCellProfile
          (WordType.proportionalCounts sourceProfile k) complement cellOf =
        WordType.proportionalCounts cellProfile k := by
    change complementaryOccurrenceCellProfile
        (WordType.proportionalCounts sourceProfile k) complement cellOf =
      WordType.proportionalCounts
        (complementaryOccurrenceCellProfile sourceProfile complement cellOf) k
    exact ComplementaryOccurrenceLaw.complementaryOccurrenceCellProfile_proportionalCounts
      sourceProfile complement cellOf k
  have hscaledJointProfile :
      (cwProportionalOccurrenceLaw law k).cellJointProfile complement cellOf =
        WordType.proportionalCounts jointProfile k := by
    change (cwProportionalOccurrenceLaw law k).cellJointProfile complement cellOf =
      WordType.proportionalCounts (law.cellJointProfile complement cellOf) k
    exact cwProportionalOccurrenceLaw_cellJointProfile law complement cellOf k
  have hscaledModel :
      (cwProportionalOccurrenceLaw law k).toCellProductProjectionModel
          complement cellOf hmass = M := by
    rfl
  have hscaledEntropy' :
      WordType.conditionalProfileEntropyBase
          (complementaryOccurrenceCellProfile
            (WordType.proportionalCounts sourceProfile k) complement cellOf)
          ((cwProportionalOccurrenceLaw law k).cellJointProfile complement cellOf) =
        Real.exp
          ((WordType.profileMass
              (WordType.proportionalCounts sourceProfile k) : ℝ) *
            ((cwProportionalOccurrenceLaw law k).toCellProductProjectionModel
            complement cellOf hmass).reference.conditionalEntropy
            ((cwProportionalOccurrenceLaw law k).toCellProductProjectionModel
              complement cellOf hmass).coarse) := by
    exact hscaledEntropy

  rw [hscaledCellProfile, hscaledJointProfile, hscaledModel] at hscaledEntropy'
  have hbaseScale :=
    WordType.conditionalProfileEntropyBase_proportionalCounts
      cellProfile jointProfile hmargin hcellMass k hk
  have hprofileMassScale :
      WordType.profileMass (WordType.proportionalCounts sourceProfile k) =
        WordType.profileMass sourceProfile * k := by
    simp only [WordType.profileMass, WordType.proportionalCounts, Finset.sum_mul]
  have hbaseExp :
      WordType.conditionalProfileEntropyBase cellProfile jointProfile ^ k =
        Real.exp ((k : ℝ) *
          ((WordType.profileMass sourceProfile : ℝ) *
            M.reference.conditionalEntropy M.coarse)) := by
    rw [← hbaseScale]
    calc
      WordType.conditionalProfileEntropyBase
          (WordType.proportionalCounts cellProfile k)
          (WordType.proportionalCounts jointProfile k) =
          Real.exp
            ((WordType.profileMass
                (WordType.proportionalCounts sourceProfile k) : ℝ) *
              M.reference.conditionalEntropy M.coarse) := hscaledEntropy'
      _ = Real.exp ((k : ℝ) *
          ((WordType.profileMass sourceProfile : ℝ) *
            M.reference.conditionalEntropy M.coarse)) := by
            rw [hprofileMassScale]
            rw [Nat.cast_mul]
            ac_rfl
  change Real.exp ((k : ℝ) *
      ((WordType.profileMass sourceProfile : ℝ) *
        M.reference.conditionalEntropy M.coarse)) ≤
    WordType.structuralZeroMultinomialLoss jointProfile k *
      ((cwRecursiveExactTargetFiberParts
        (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
        targets reference logicalLeg).card : ℝ)
  calc
    Real.exp ((k : ℝ) *
        ((WordType.profileMass sourceProfile : ℝ) *
          M.reference.conditionalEntropy M.coarse)) =
        WordType.conditionalProfileEntropyBase cellProfile jointProfile ^ k :=
      hbaseExp.symm
    _ ≤ WordType.structuralZeroMultinomialLoss jointProfile k *
        ((WordType.conditionalTypeClass source
          (WordType.proportionalCounts jointProfile k)).card : ℝ) := hconditional
    _ = WordType.structuralZeroMultinomialLoss jointProfile k *
        ((cwRecursiveExactTargetFiberParts
          (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
          targets reference logicalLeg).card : ℝ) := by rw [hcards]

end AlgebraicComplexity.Examples
