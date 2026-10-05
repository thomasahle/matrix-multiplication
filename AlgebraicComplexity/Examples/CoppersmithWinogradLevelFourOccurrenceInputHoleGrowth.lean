/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ExponentialTailAbsorption
import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceInputHoleBound

set_option autoImplicit false

/-!
# Asymptotic absorption of level-four occurrence input holes

The finite level-four concentration theorem has a polynomial type-selection factor, one
structural-zero multinomial loss, and a strict exponential entropy deficit.  This file packages
the first two factors as one positive subexponential sequence and applies the generic
division-free tail comparison.

The final theorem deliberately keeps the matching lower bound for the exact target family as a
pointwise premise.  Thus it proves the analytic passage needed by sparse repair without assuming
that a concrete target-cardinality expression has already been identified with the occurrence
model's conditional entropy.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentLevelFourValidity
open MatrixMultiplication.SimplifiedRecursiveLevelFourOccurrences
open MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles
open MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-- One subexponential loss dominating the literal level-four occurrence type-selection factor
and its structural-zero multinomial loss. -/
noncomputable def levelFourOccurrenceInputHoleLoss
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (k : ℕ) : ℝ :=
  let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
  let d := Fintype.card
    (LevelFourValidSlot parent × (SplitWord 2 × SplitWord 2))
  ((((WordType.profileMass sourceProfile + 1) ^ d : ℕ) : ℝ)) *
    ((((k + 1) ^ d : ℕ) : ℝ)) *
      WordType.structuralZeroMultinomialLoss sourceProfile k

/-- The packaged level-four input-hole loss is positive at every repetition. -/
theorem levelFourOccurrenceInputHoleLoss_pos
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (k : ℕ) :
    0 < levelFourOccurrenceInputHoleLoss top root region parent k := by
  unfold levelFourOccurrenceInputHoleLoss
  exact mul_pos (mul_pos (by positivity) (by positivity))
    (WordType.structuralZeroMultinomialLoss_pos _ _)

/-- The literal type-selection factor in the finite concentration theorem is bounded by the
separated constant-times-polynomial loss. -/
theorem levelFourOccurrenceTypeSelection_mul_structuralZeroLoss_le_inputHoleLoss
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) (k : ℕ) :
    let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
    ((((WordType.profileMass sourceProfile * k + 1) ^
          Fintype.card
            (LevelFourValidSlot parent × (SplitWord 2 × SplitWord 2)) : ℕ) : ℝ)) *
        WordType.structuralZeroMultinomialLoss sourceProfile k ≤
      levelFourOccurrenceInputHoleLoss top root region parent k := by
  let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
  let d := Fintype.card
    (LevelFourValidSlot parent × (SplitWord 2 × SplitWord 2))
  have hbase : WordType.profileMass sourceProfile * k + 1 ≤
      (WordType.profileMass sourceProfile + 1) * (k + 1) := by
    nlinarith [Nat.zero_le (WordType.profileMass sourceProfile), Nat.zero_le k]
  have hpow : (WordType.profileMass sourceProfile * k + 1) ^ d ≤
      (WordType.profileMass sourceProfile + 1) ^ d * (k + 1) ^ d := by
    simpa only [mul_pow] using pow_le_pow_left' hbase d
  have hpowReal :
      ((((WordType.profileMass sourceProfile * k + 1) ^ d : ℕ) : ℝ)) ≤
        ((((WordType.profileMass sourceProfile + 1) ^ d : ℕ) : ℝ)) *
          ((((k + 1) ^ d : ℕ) : ℝ)) := by
    exact_mod_cast hpow
  unfold levelFourOccurrenceInputHoleLoss
  dsimp only [sourceProfile, d] at hpowReal ⊢
  exact mul_le_mul_of_nonneg_right hpowReal
    (WordType.structuralZeroMultinomialLoss_pos sourceProfile k).le

/-- The complete level-four occurrence input-hole loss is subexponential. -/
theorem levelFourOccurrenceInputHoleLoss_subexponential
    (top : TopBranchRows) (root region : Fin 6)
    (parent : Fin positiveLevelFourShapeCount) :
    Growth.Subexponential
      (levelFourOccurrenceInputHoleLoss top root region parent) := by
  let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
  let d := Fintype.card
    (LevelFourValidSlot parent × (SplitWord 2 × SplitWord 2))
  let constant : ℝ :=
    ((((WordType.profileMass sourceProfile + 1) ^ d : ℕ) : ℝ))
  have htype : Growth.Subexponential (fun k : ℕ ↦
      constant * ((((k + 1) ^ d : ℕ) : ℝ))) := by
    simpa only [constant, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      (Growth.Subexponential.natCast_succ_pow d).const_mul
        (show 0 ≤ constant by positivity)
  have hzero := WordType.structuralZeroMultinomialLoss_subexponential sourceProfile
  change Growth.Subexponential (fun k ↦
    ((((WordType.profileMass
          (levelFourOccurrenceSourceProfile top root region parent) + 1) ^
        Fintype.card
          (LevelFourValidSlot parent × (SplitWord 2 × SplitWord 2)) : ℕ) : ℝ)) *
      ((((k + 1) ^
        Fintype.card
          (LevelFourValidSlot parent × (SplitWord 2 × SplitWord 2)) : ℕ) : ℝ)) *
        WordType.structuralZeroMultinomialLoss
          (levelFourOccurrenceSourceProfile top root region parent) k)
  simpa only [sourceProfile, d, constant] using htype.mul hzero

/-- Finite level-four occurrence concentration with every nonexponential factor packaged into
`levelFourOccurrenceInputHoleLoss`. -/
theorem card_levelFourOccurrenceInputProfileHoles_le_inputHoleLoss_mul_exp
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
      levelFourOccurrenceInputHoleLoss top root region parent k *
        Real.exp (((k : ℝ) * WordType.profileMass sourceProfile) *
          (M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4)) := by
  have hfinite := card_levelFourOccurrenceInputProfileHoles_le
    top betaThree order sigma horder root region parent hvalid hboundary k n hk hparent hsamples
      hepsilon reference hreference logicalLeg
  have hloss :=
    levelFourOccurrenceTypeSelection_mul_structuralZeroLoss_le_inputHoleLoss
      top root region parent k
  dsimp only at hfinite ⊢
  exact hfinite.trans
    (mul_le_mul_of_nonneg_right hloss (Real.exp_nonneg _))

/-- **Repair-ready asymptotic input-hole bound.**

Assume only a pointwise lower bound on the exact target count with the same leading conditional
entropy as the occurrence projection model, up to a positive subexponential target loss.  Then
every fixed natural repair budget eventually times the input-hole count is at most that target
count.  The cutoff is uniform in the marked reference, logical leg, and target cardinality. -/
theorem eventually_budget_mul_card_levelFourOccurrenceInputProfileHoles_le_of_targetGrowth
    (top : TopBranchRows) (betaThree : BetaThreeRows)
    (order : CoordinateOrder) (sigma : Orientation)
    (horder : CoordinateOrder.AgreesWithOrientation order sigma)
    (root region : Fin 6) (parent : Fin positiveLevelFourShapeCount)
    (hvalid : LevelFourChildRowsValid top betaThree root region parent sigma)
    (hboundary : FixedParentSlotBoundaryValid
      top betaThree order root.val region.val parent.val)
    (hparent : 0 < levelFourParentSamples top root region parent)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (targetLoss : ℕ → ℝ) (htargetLoss : Growth.Subexponential targetLoss)
    (budget : ℕ) :
    ∃ cutoff : ℕ, ∀ k n : ℕ, cutoff ≤ k → ∀ hk : 0 < k,
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
      ∀ (logicalLeg : Leg) (targetCard : ℕ),
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
          targetLoss k * (targetCard : ℝ) →
        budget *
            (cwRecursiveInputProfileHoles
              (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
              (levelFourOccurrenceParentTerm
                top betaThree root region parent sigma hvalid k)
              (levelFourOccurrenceParentTerm_multiplicity_eq_succ
                top betaThree root region parent sigma hvalid k n hsamples)
              epsilon scaledData.toCompatibilityTargets reference logicalLeg).card ≤
          targetCard := by
  let sourceProfile := levelFourOccurrenceSourceProfile top root region parent
  have hsourceMass : 0 < WordType.profileMass sourceProfile := by
    change 0 < WordType.profileMass
      (levelFourOccurrenceSourceProfile top root region parent)
    rw [profileMass_levelFourOccurrenceSourceProfile]
    exact hparent
  let rate : ℝ :=
    (WordType.profileMass sourceProfile : ℝ) * epsilon ^ 2 / 4
  have hrate : 0 < rate := by
    dsimp only [rate]
    exact div_pos
      (mul_pos (by exact_mod_cast hsourceMass) (sq_pos_of_pos hepsilon)) (by norm_num)
  obtain ⟨cutoff, hcutoff⟩ :=
    Growth.Subexponential.eventually_budget_mul_bad_le_target_of_common_exponential_bounds
      (levelFourOccurrenceInputHoleLoss_subexponential top root region parent)
      htargetLoss hrate budget
  refine ⟨cutoff, ?_⟩
  intro k n hkCutoff hk hsamples reference hreference logicalLeg targetCard
  dsimp only
  intro htarget
  let scaledData := cwProportionalRecursiveOccurrenceTargetData
    (levelFourOccurrenceTargetData top betaThree order sigma horder root region parent
      hvalid hboundary) k
  let hmass := cwProportionalProfileMass_pos sourceProfile hsourceMass k hk
  let M := cwRecursiveOccurrenceProjectionModel
    (levelFourOccurrenceCoarseIndex parent sigma) scaledData logicalLeg
      (levelFourComplementSlotPerm parent)
      (levelFourOccurrenceCoarseIndex_total parent sigma) hmass
  let holes := cwRecursiveInputProfileHoles
    (fun _ ↦ PUnit.unit) (Equiv.refl Leg)
    (levelFourOccurrenceParentTerm top betaThree root region parent sigma hvalid k)
    (levelFourOccurrenceParentTerm_multiplicity_eq_succ
      top betaThree root region parent sigma hvalid k n hsamples)
    epsilon scaledData.toCompatibilityTargets reference logicalLeg
  have hbad := card_levelFourOccurrenceInputProfileHoles_le_inputHoleLoss_mul_exp
    top betaThree order sigma horder root region parent hvalid hboundary k n hk hparent hsamples
      hepsilon.le reference hreference logicalLeg
  have hexponent :
      ((k : ℝ) * WordType.profileMass sourceProfile) *
          (M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4) =
        (k : ℝ) *
          ((WordType.profileMass sourceProfile : ℝ) *
              M.reference.conditionalEntropy M.coarse - rate) := by
    dsimp only [rate]
    ring
  have hbad' :
      (holes.card : ℝ) ≤
        levelFourOccurrenceInputHoleLoss top root region parent k *
          Real.exp ((k : ℝ) *
            ((WordType.profileMass sourceProfile : ℝ) *
                M.reference.conditionalEntropy M.coarse - rate)) := by
    simpa only [sourceProfile, scaledData, hmass, M, holes, hexponent] using hbad
  have htarget' :
      Real.exp ((k : ℝ) *
          ((WordType.profileMass sourceProfile : ℝ) *
            M.reference.conditionalEntropy M.coarse)) ≤
        targetLoss k * (targetCard : ℝ) := by
    simpa only [sourceProfile, scaledData, hmass, M] using htarget
  exact hcutoff k holes.card targetCard
    ((WordType.profileMass sourceProfile : ℝ) *
      M.reference.conditionalEntropy M.coarse) hkCutoff hbad' htarget'

end AlgebraicComplexity.Examples
