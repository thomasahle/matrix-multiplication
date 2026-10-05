/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.BehrendRate
import AlgebraicComplexity.Analysis.ConditionalLegFiberGrowth
import AlgebraicComplexity.Analysis.EventualCopyGrowth
import AlgebraicComplexity.Combinatorics.PrimeFieldSizing
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerPrimeHashing

set_option autoImplicit false

/-!
# Exponential growth of the total-weight inner hashing field

This module turns the exact stabilizer double count for a fixed total-weight quotient word into
an asymptotic bound for its canonical inner hashing field.  The exponential field base is not an
all-words alphabet bound: it is the quotient

`ambientBase / conditionalLegBase`.

Here `conditionalLegBase` is the exact entropy base of the joint `(coarse support, fine leg)`
profile over the fixed coarse word.  An ambient-family upper bound remains an explicit input,
because using a global maximum-entropy envelope and using the sharper conditional envelope are
mathematically different rate statements.  This makes the accounting boundary visible to the
certificate client and prevents an accidental double count of the outer quotient entropy.
-/

namespace AlgebraicComplexity.Examples

open scoped BigOperators
open AlgebraicComplexity Tensor

universe u

/-- Exact joint profile after pushing a fine chunk-support profile to total-weight support. -/
noncomputable def cwTotalWeightCoarseProfile
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ) :
    CWTotalWeightCoarseSupport K q depth → ℕ :=
  WordType.mappedType
    ((cwChunkPartitionedTensor K q depth).coarseningSupportMap
      (cwTotalWeightChunkCoarsening depth)) profile

/-- Pushing a proportional fine profile commutes with the total-weight quotient. -/
theorem cwTotalWeightCoarseProfile_proportionalCounts
    (K : Type u) [CommRing K] (q depth k : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ) :
    cwTotalWeightCoarseProfile K q depth
        (WordType.proportionalCounts profile k) =
      WordType.proportionalCounts
        (cwTotalWeightCoarseProfile K q depth profile) k := by
  exact WordType.mappedType_proportionalCounts _ profile k

/-- The quotient preserves the primitive profile mass. -/
theorem cwTotalWeightCoarseProfile_mass
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ) :
    WordType.profileMass (cwTotalWeightCoarseProfile K q depth profile) =
      WordType.profileMass profile :=
  WordType.profileMass_mappedType _ profile

/-- The exact `(coarse support, fine leg)` profile has the quotient profile as first marginal. -/
theorem cwTotalWeightConditionalLegType_fst
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (c : Leg) :
    WordType.mappedType Prod.fst
        (cwTotalWeightConditionalLegType K q depth profile c) =
      cwTotalWeightCoarseProfile K q depth profile := by
  unfold cwTotalWeightConditionalLegType cwTotalWeightCoarseProfile
  rw [WordType.mappedType_comp]
  rfl

/-- Conditional leg profiles scale exactly along proportional repetitions. -/
theorem cwTotalWeightConditionalLegType_proportionalCounts
    (K : Type u) [CommRing K] (q depth k : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (c : Leg) :
    cwTotalWeightConditionalLegType K q depth
        (WordType.proportionalCounts profile k) c =
      WordType.proportionalCounts
        (cwTotalWeightConditionalLegType K q depth profile c) k := by
  exact WordType.mappedType_proportionalCounts _ profile k

/-- Exact conditional entropy base for one fine leg after a joint total-weight word is fixed. -/
noncomputable def cwTotalWeightConditionalLegEntropyBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (c : Leg) : ℝ :=
  WordType.conditionalProfileEntropyBase
    (cwTotalWeightCoarseProfile K q depth profile)
    (cwTotalWeightConditionalLegType K q depth profile c)

theorem cwTotalWeightConditionalLegEntropyBase_pos
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (c : Leg) :
    0 < cwTotalWeightConditionalLegEntropyBase K q depth profile c :=
  WordType.conditionalProfileEntropyBase_pos _ _

/-- Exponential base of all exact fine-profile lifts of one fixed total-weight support word. -/
noncomputable def cwTotalWeightInnerTargetBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ) : ℝ :=
  WordType.pushedTypeFiberEntropyBase
    ((cwChunkPartitionedTensor K q depth).coarseningSupportMap
      (cwTotalWeightChunkCoarsening depth)) profile

theorem cwTotalWeightInnerTargetBase_pos
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ) :
    0 < cwTotalWeightInnerTargetBase K q depth profile :=
  WordType.pushedTypeFiberEntropyBase_pos _ _

/-- Every supported coarse word of the exact pushed proportional type contains the full uniform
fine target family with quotient entropy base `cwTotalWeightInnerTargetBase`. -/
theorem cwTotalWeightInnerTargetBase_pow_le_markedFiber
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k)
    (hlen : WordType.profileMass profile * k = n + 1)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hcoarseWord : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord) =
      WordType.proportionalCounts
        (cwTotalWeightCoarseProfile K q depth profile) k) :
    cwTotalWeightInnerTargetBase K q depth profile ^ k ≤
      WordType.pushedTypeFiberLoss profile k *
        ((cwTotalWeightMarkedFiberWords K q depth n
          (WordType.proportionalCounts profile k) coarseWord).card : ℝ) := by
  have htarget :
      positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord ∈
        WordType.typeClass (n + 1)
          (WordType.proportionalCounts
            (cwTotalWeightCoarseProfile K q depth profile) k) := by
    rw [WordType.mem_typeClass]
    exact hcoarseWord
  have hbound :=
    WordType.pushedTypeFiberEntropyBase_pow_le_loss_mul_card_typedFiber_of_length_eq
      ((cwChunkPartitionedTensor K q depth).coarseningSupportMap
        (cwTotalWeightChunkCoarsening depth))
      profile hprofileMass k hk hlen
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
      (by simpa only [cwTotalWeightCoarseProfile] using htarget)
  rw [cwTotalWeightInnerTargetBase]
  rw [card_cwTotalWeightMarkedFiberWords]
  exact hbound

/-- Largest of the three conditional competitor quotients.  The outer `max 1` is the canonical
normalization expected by prime-field growth, including degenerate small bases. -/
noncomputable def cwTotalWeightInnerCompetitorBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientBase : ℝ) : ℝ :=
  max 1 <| max
    (ambientBase / cwTotalWeightConditionalLegEntropyBase K q depth profile .X) <|
    max
      (ambientBase / cwTotalWeightConditionalLegEntropyBase K q depth profile .Y)
      (ambientBase / cwTotalWeightConditionalLegEntropyBase K q depth profile .Z)

theorem one_le_cwTotalWeightInnerCompetitorBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientBase : ℝ) :
    1 ≤ cwTotalWeightInnerCompetitorBase K q depth profile ambientBase :=
  le_max_left _ _

theorem div_conditionalLegEntropyBase_le_innerCompetitorBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientBase : ℝ) (c : Leg) :
    ambientBase / cwTotalWeightConditionalLegEntropyBase K q depth profile c ≤
      cwTotalWeightInnerCompetitorBase K q depth profile ambientBase := by
  cases c with
  | X => exact (le_max_left _ _).trans (le_max_right _ _)
  | Y => exact (le_max_left _ _).trans (le_max_right _ _ |>.trans (le_max_right _ _))
  | Z => exact (le_max_right _ _).trans (le_max_right _ _ |>.trans (le_max_right _ _))

/-- Copy base delivered by localized marked hashing before the subexponential Behrend loss. -/
noncomputable def cwTotalWeightInnerCopyBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientBase : ℝ) : ℝ :=
  cwTotalWeightInnerTargetBase K q depth profile /
    cwTotalWeightInnerCompetitorBase K q depth profile ambientBase

theorem cwTotalWeightInnerCopyBase_pos
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientBase : ℝ) :
    0 < cwTotalWeightInnerCopyBase K q depth profile ambientBase := by
  exact div_pos (cwTotalWeightInnerTargetBase_pos K q depth profile)
    (zero_lt_one.trans_le
      (one_le_cwTotalWeightInnerCompetitorBase K q depth profile ambientBase))

/-- Exact logarithmic rate accounting: the inner copy exponent is target-fiber entropy minus
the largest conditional competitor-field exponent. -/
theorem log_cwTotalWeightInnerCopyBase
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientBase : ℝ) :
    Real.log (cwTotalWeightInnerCopyBase K q depth profile ambientBase) =
      Real.log (cwTotalWeightInnerTargetBase K q depth profile) -
        Real.log (cwTotalWeightInnerCompetitorBase K q depth profile ambientBase) := by
  unfold cwTotalWeightInnerCopyBase
  exact Real.log_div
    (cwTotalWeightInnerTargetBase_pos K q depth profile).ne'
    (zero_lt_one.trans_le
      (one_le_cwTotalWeightInnerCompetitorBase K q depth profile ambientBase)).ne'

/-- A positive subexponential loss multiplying an assumed localized-ambient upper loss. -/
noncomputable def cwTotalWeightInnerCompetitorInputLoss
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientLoss : ℕ → ℝ) (k : ℕ) : ℝ :=
  12 * ambientLoss k *
    (∑ c : Leg, WordType.structuralZeroMultinomialLoss
      (cwTotalWeightConditionalLegType K q depth profile c) k)

theorem cwTotalWeightInnerCompetitorInputLoss_pos
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientLoss : ℕ → ℝ) (hambientLoss : ∀ k, 0 < ambientLoss k)
    (k : ℕ) :
    0 < cwTotalWeightInnerCompetitorInputLoss
      K q depth profile ambientLoss k := by
  unfold cwTotalWeightInnerCompetitorInputLoss
  have hsum : 0 < ∑ c : Leg, WordType.structuralZeroMultinomialLoss
      (cwTotalWeightConditionalLegType K q depth profile c) k := by
    exact Finset.sum_pos (fun c _ ↦
      WordType.structuralZeroMultinomialLoss_pos
        (cwTotalWeightConditionalLegType K q depth profile c) k)
      ⟨.X, Finset.mem_univ _⟩
  exact mul_pos (mul_pos (by norm_num) (hambientLoss k)) hsum

/-- The packaged field-input loss is subexponential whenever the localized ambient upper loss
is. -/
theorem cwTotalWeightInnerCompetitorInputLoss_subexponential
    (K : Type u) [CommRing K] (q depth : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (ambientLoss : ℕ → ℝ)
    (hambientLoss : Growth.Subexponential ambientLoss) :
    Growth.Subexponential
      (cwTotalWeightInnerCompetitorInputLoss K q depth profile ambientLoss) := by
  have hsum : Growth.Subexponential (fun k ↦
      ∑ c : Leg, WordType.structuralZeroMultinomialLoss
        (cwTotalWeightConditionalLegType K q depth profile c) k) := by
    exact Growth.Subexponential.fintype_sum
      (fun c k ↦ WordType.structuralZeroMultinomialLoss
        (cwTotalWeightConditionalLegType K q depth profile c) k)
      (fun c ↦ WordType.structuralZeroMultinomialLoss_subexponential
        (cwTotalWeightConditionalLegType K q depth profile c))
  change Growth.Subexponential (fun k ↦ 12 * ambientLoss k *
    ∑ c : Leg, WordType.structuralZeroMultinomialLoss
      (cwTotalWeightConditionalLegType K q depth profile c) k)
  exact (hambientLoss.const_mul (by norm_num : (0 : ℝ) ≤ 12)).mul hsum

/-- Cast an exact natural-valued finite supremum through a real upper bound. -/
theorem natCast_finsetSup_le {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℕ) (upper : ℝ)
    (hupper : 0 ≤ upper)
    (h : ∀ i ∈ s, (f i : ℝ) ≤ upper) :
    ((s.sup f : ℕ) : ℝ) ≤ upper := by
  induction s using Finset.induction_on with
  | empty => simpa using hupper
  | @insert i s hi ih =>
      rw [Finset.sup_insert, Nat.cast_max, max_le_iff]
      exact ⟨h i (Finset.mem_insert_self i s),
        ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))⟩

/-- One exact localized source-word leg fiber has quotient entropy base
`ambientBase / conditionalLegBase`.

The premise `hambient` is deliberately local to the fixed coarse word.  Supplying a global
fixed-marginal bound is always sound but may be weaker; a conditional maximum-entropy theorem can
instead supply the sharp bound without changing this finite proof. -/
theorem cwTotalWeight_sourceWordLegFiber_card_le_entropyQuotient
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (profile : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k)
    (hlen : WordType.profileMass profile * k = n + 1)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n)
    (hcoarseWord : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord) =
      WordType.proportionalCounts
        (cwTotalWeightCoarseProfile K q depth profile) k)
    (ambientBase ambientLoss : ℝ)
    (hambient :
      ((cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts profile k) coarseWord).card : ℝ) ≤
        ambientLoss * ambientBase ^ k)
    (markedWord : PositiveWord (cwChunkPartitionedTensor K q depth).support n)
    (hmarkedWord : markedWord ∈ cwTotalWeightMarkedFiberWords K q depth n
      (WordType.proportionalCounts profile k) coarseWord)
    (c : Leg) :
    ((PartitionHashEncoding.sourceWordLegFiber n
      (cwTotalWeightLocalizedAmbientWords K q depth n
        (WordType.proportionalCounts profile k) coarseWord) c
      (PartitionHashEncoding.supportWordAddress n markedWord c)).card : ℝ) ≤
      (WordType.structuralZeroMultinomialLoss
          (cwTotalWeightConditionalLegType K q depth profile c) k * ambientLoss) *
        (ambientBase /
          cwTotalWeightConditionalLegEntropyBase K q depth profile c) ^ k := by
  let coarseProfile := cwTotalWeightCoarseProfile K q depth profile
  let jointProfile := cwTotalWeightConditionalLegType K q depth profile c
  let conditionalCard := (WordType.conditionalTypeClass
    (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
    (WordType.proportionalCounts jointProfile k)).card
  let fiberCard := (PartitionHashEncoding.sourceWordLegFiber n
    (cwTotalWeightLocalizedAmbientWords K q depth n
      (WordType.proportionalCounts profile k) coarseWord) c
    (PartitionHashEncoding.supportWordAddress n markedWord c)).card
  let ambientCard := (cwTotalWeightLocalizedAmbientWords K q depth n
    (WordType.proportionalCounts profile k) coarseWord).card
  have hcoarseMass : 0 < WordType.profileMass coarseProfile := by
    simpa only [coarseProfile, cwTotalWeightCoarseProfile_mass] using hprofileMass
  have hlength : WordType.profileMass coarseProfile * k = n + 1 := by
    simpa only [coarseProfile, cwTotalWeightCoarseProfile_mass] using hlen
  have hconditional :
      cwTotalWeightConditionalLegEntropyBase K q depth profile c ^ k ≤
        WordType.structuralZeroMultinomialLoss jointProfile k *
          (conditionalCard : ℝ) := by
    exact WordType.conditionalProfileEntropyBase_pow_le_structuralZeroLoss_mul_card_of_length_eq
      coarseProfile jointProfile
      (cwTotalWeightConditionalLegType_fst K q depth profile c)
      hcoarseMass k hk hlength
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n coarseWord)
      hcoarseWord
  have hdouble : conditionalCard * fiberCard ≤ ambientCard := by
    have hfinite :=
      cwTotalWeight_card_conditionalLegType_mul_card_markedSourceWordLegFiber_le
        K q depth n (WordType.proportionalCounts profile k) coarseWord
        markedWord hmarkedWord c
    simpa only [conditionalCard, fiberCard, ambientCard,
      cwTotalWeightConditionalLegType_proportionalCounts] using hfinite
  exact WordType.fiberCard_le_mul_div_pow_of_conditional_mul_fiber_le
    (cwTotalWeightConditionalLegEntropyBase K q depth profile c)
    ambientBase
    (WordType.structuralZeroMultinomialLoss jointProfile k)
    ambientLoss k conditionalCard fiberCard ambientCard
    (cwTotalWeightConditionalLegEntropyBase_pos K q depth profile c)
    (WordType.structuralZeroMultinomialLoss_pos jointProfile k).le
    hconditional hdouble hambient

/-- Exact exponential upper bound for the maximum localized competitor requirement.  Its base is
the maximum of the three conditional quotients and its only additional factor is the positive
subexponential conditional-type loss. -/
theorem cwTotalWeightInnerCompetitorRequirement_cast_le
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k)
    (hlen : WordType.profileMass profile * k = n + 1)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n)
    (hcoarseWord : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q 1) n coarseWord) =
      WordType.proportionalCounts (cwTotalWeightCoarseProfile K q 1 profile) k)
    (ambientBase : ℝ) (hambientBase : 0 ≤ ambientBase)
    (ambientLoss : ℕ → ℝ)
    (hambientLoss : 0 < ambientLoss k)
    (hambient :
      ((cwTotalWeightLocalizedAmbientWords K q 1 n
        (WordType.proportionalCounts profile k) coarseWord).card : ℝ) ≤
        ambientLoss k * ambientBase ^ k) :
    (cwTotalWeightInnerCompetitorRequirement K q n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
      cwTotalWeightInnerCompetitorInputLoss K q 1 profile ambientLoss k *
        cwTotalWeightInnerCompetitorBase K q 1 profile ambientBase ^ k := by
  let base := cwTotalWeightInnerCompetitorBase K q 1 profile ambientBase
  let sumLoss := ∑ c : Leg, WordType.structuralZeroMultinomialLoss
    (cwTotalWeightConditionalLegType K q 1 profile c) k
  have hbase : 0 ≤ base :=
    (one_le_cwTotalWeightInnerCompetitorBase K q 1 profile ambientBase).trans'
      (by norm_num)
  have hsumNonneg : 0 ≤ sumLoss := by
    exact Finset.sum_nonneg fun c _ ↦
      (WordType.structuralZeroMultinomialLoss_pos
        (cwTotalWeightConditionalLegType K q 1 profile c) k).le
  have hcommon : ∀ c : Leg,
      WordType.structuralZeroMultinomialLoss
          (cwTotalWeightConditionalLegType K q 1 profile c) k * ambientLoss k *
        (ambientBase /
          cwTotalWeightConditionalLegEntropyBase K q 1 profile c) ^ k ≤
      ambientLoss k * sumLoss * base ^ k := by
    intro c
    have hloss : WordType.structuralZeroMultinomialLoss
        (cwTotalWeightConditionalLegType K q 1 profile c) k ≤ sumLoss := by
      exact Finset.single_le_sum
        (fun d _ ↦ (WordType.structuralZeroMultinomialLoss_pos
          (cwTotalWeightConditionalLegType K q 1 profile d) k).le)
        (Finset.mem_univ c)
    have hratioNonneg : 0 ≤ ambientBase /
        cwTotalWeightConditionalLegEntropyBase K q 1 profile c :=
      div_nonneg hambientBase
        (cwTotalWeightConditionalLegEntropyBase_pos K q 1 profile c).le
    have hpow : (ambientBase /
        cwTotalWeightConditionalLegEntropyBase K q 1 profile c) ^ k ≤ base ^ k :=
      pow_le_pow_left₀ hratioNonneg
        (div_conditionalLegEntropyBase_le_innerCompetitorBase
          K q 1 profile ambientBase c) k
    calc
      WordType.structuralZeroMultinomialLoss
            (cwTotalWeightConditionalLegType K q 1 profile c) k * ambientLoss k *
          (ambientBase /
            cwTotalWeightConditionalLegEntropyBase K q 1 profile c) ^ k =
        WordType.structuralZeroMultinomialLoss
            (cwTotalWeightConditionalLegType K q 1 profile c) k *
          (ambientLoss k * (ambientBase /
            cwTotalWeightConditionalLegEntropyBase K q 1 profile c) ^ k) := by ring
      _ ≤ sumLoss * (ambientLoss k * (ambientBase /
            cwTotalWeightConditionalLegEntropyBase K q 1 profile c) ^ k) :=
        mul_le_mul_of_nonneg_right hloss
          (mul_nonneg hambientLoss.le (pow_nonneg hratioNonneg k))
      _ ≤ sumLoss * (ambientLoss k * base ^ k) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow hambientLoss.le) hsumNonneg
      _ = ambientLoss k * sumLoss * base ^ k := by ring
  have hmaximum :
      (cwTotalWeightInnerLegFiberMaximum K q n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
      ambientLoss k * sumLoss * base ^ k := by
    unfold cwTotalWeightInnerLegFiberMaximum
    apply natCast_finsetSup_le
    · exact mul_nonneg (mul_nonneg hambientLoss.le hsumNonneg) (pow_nonneg hbase k)
    intro c hc
    apply natCast_finsetSup_le
    · exact mul_nonneg (mul_nonneg hambientLoss.le hsumNonneg) (pow_nonneg hbase k)
    intro markedWord hmarkedWord
    exact (cwTotalWeight_sourceWordLegFiber_card_le_entropyQuotient
      K q 1 n profile hprofileMass k hk hlen coarseWord hcoarseWord
      ambientBase (ambientLoss k) hambient
      markedWord hmarkedWord c).trans (hcommon c)
  unfold cwTotalWeightInnerCompetitorRequirement
    cwTotalWeightInnerCompetitorInputLoss
  push_cast
  change 12 *
      (cwTotalWeightInnerLegFiberMaximum K q n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
    12 * ambientLoss k * sumLoss * base ^ k
  calc
    12 * (cwTotalWeightInnerLegFiberMaximum K q n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
      12 * (ambientLoss k * sumLoss * base ^ k) :=
        mul_le_mul_of_nonneg_left hmaximum (show (0 : ℝ) ≤ 12 by norm_num)
    _ = 12 * ambientLoss k * sumLoss * base ^ k := by ring

/-- The canonical next-prime hashing field has exactly the same conditional competitor base. -/
theorem cwTotalWeightInnerHashModulus_cast_le
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k)
    (hlen : WordType.profileMass profile * k = n + 1)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n)
    (hcoarseWord : WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q 1) n coarseWord) =
      WordType.proportionalCounts (cwTotalWeightCoarseProfile K q 1 profile) k)
    (ambientBase : ℝ) (hambientBase : 0 ≤ ambientBase)
    (ambientLoss : ℕ → ℝ)
    (hambientLoss : 0 < ambientLoss k)
    (hambient :
      ((cwTotalWeightLocalizedAmbientWords K q 1 n
        (WordType.proportionalCounts profile k) coarseWord).card : ℝ) ≤
        ambientLoss k * ambientBase ^ k) :
    (cwTotalWeightInnerHashModulus K q n
        (WordType.proportionalCounts profile k) coarseWord : ℝ) ≤
      PrimeFieldSizing.loss 9
          (cwTotalWeightInnerCompetitorInputLoss K q 1 profile ambientLoss) k *
        cwTotalWeightInnerCompetitorBase K q 1 profile ambientBase ^ k := by
  simpa only [cwTotalWeightInnerHashModulus, PrimeFieldSizing.loss, add_assoc] using
    (PrimeFieldSizing.modulus_cast_le_loss_mul_pow
      9
      (cwTotalWeightInnerCompetitorRequirement K q n
        (WordType.proportionalCounts profile k) coarseWord)
      k
      (cwTotalWeightInnerCompetitorInputLoss K q 1 profile ambientLoss k)
      (cwTotalWeightInnerCompetitorBase K q 1 profile ambientBase)
      (one_le_cwTotalWeightInnerCompetitorBase K q 1 profile ambientBase)
      (cwTotalWeightInnerCompetitorRequirement_cast_le
        K q n profile hprofileMass k hk hlen coarseWord hcoarseWord
        ambientBase hambientBase ambientLoss hambientLoss hambient))

/-! ## Sequence-ready packaging -/

/-- Exact proportional coarse-word sequence together with the one genuinely quantitative input:
a sharp localized-ambient cardinality upper bound.  A certificate may prove that bound through a
conditional maximum-entropy dual; the finite hashing theorem does not need to know how it was
obtained. -/
structure CWTotalWeightInnerGrowthData
    (K : Type u) [CommRing K] (q : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (ambientBase : ℝ) (ambientLoss : ℕ → ℝ) where
  exponent : ℕ → ℕ
  coarseWord : ∀ k,
    PositiveWord (CWTotalWeightCoarseSupport K q 1) (exponent k)
  length_eq : ∀ k, 0 < k →
    WordType.profileMass profile * k = exponent k + 1
  coarse_type : ∀ k, 0 < k →
    WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q 1) (exponent k)
          (coarseWord k)) =
      WordType.proportionalCounts (cwTotalWeightCoarseProfile K q 1 profile) k
  ambientBase_nonneg : 0 ≤ ambientBase
  ambientLoss_pos : ∀ k, 0 < ambientLoss k
  ambientLoss_subexponential : Growth.Subexponential ambientLoss
  ambient_upper : ∀ k, 0 < k →
    ((cwTotalWeightLocalizedAmbientWords K q 1 (exponent k)
      (WordType.proportionalCounts profile k) (coarseWord k)).card : ℝ) ≤
        ambientLoss k * ambientBase ^ k

namespace CWTotalWeightInnerGrowthData

variable {K : Type u} [CommRing K] {q : ℕ}
variable {profile : (cwChunkPartitionedTensor K q 1).support → ℕ}
variable {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}

/-- Exact competitor requirement sequence attached to the chosen coarse representatives. -/
noncomputable def requirement
    (data : CWTotalWeightInnerGrowthData K q profile ambientBase ambientLoss)
    (k : ℕ) : ℕ :=
  cwTotalWeightInnerCompetitorRequirement K q (data.exponent k)
    (WordType.proportionalCounts profile k) (data.coarseWord k)

/-- Canonical next-prime modulus sequence. -/
noncomputable def modulus
    (data : CWTotalWeightInnerGrowthData K q profile ambientBase ambientLoss)
    (k : ℕ) : ℕ :=
  PrimeFieldSizing.modulus 9 (data.requirement k)

/-- Complete prime-field loss: exact conditional counting followed by Bertrand. -/
noncomputable def fieldLoss
    (_data : CWTotalWeightInnerGrowthData K q profile ambientBase ambientLoss)
    (k : ℕ) : ℝ :=
  PrimeFieldSizing.loss 9
    (cwTotalWeightInnerCompetitorInputLoss K q 1 profile ambientLoss) k

theorem fieldLoss_pos
    (data : CWTotalWeightInnerGrowthData K q profile ambientBase ambientLoss)
    (k : ℕ) : 0 < data.fieldLoss k := by
  unfold fieldLoss PrimeFieldSizing.loss
  have hinput := cwTotalWeightInnerCompetitorInputLoss_pos
    K q 1 profile ambientLoss data.ambientLoss_pos k
  positivity

theorem fieldLoss_subexponential
    (data : CWTotalWeightInnerGrowthData K q profile ambientBase ambientLoss) :
    Growth.Subexponential data.fieldLoss := by
  exact PrimeFieldSizing.loss_subexponential 9
    (cwTotalWeightInnerCompetitorInputLoss_subexponential
      K q 1 profile ambientLoss data.ambientLoss_subexponential)

/-- The canonical prime fields grow at the exact conditional competitor base, with no hidden
all-words maximum. -/
theorem modulus_cast_le_fieldLoss_mul_pow
    (data : CWTotalWeightInnerGrowthData K q profile ambientBase ambientLoss)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k) :
    (data.modulus k : ℝ) ≤ data.fieldLoss k *
      cwTotalWeightInnerCompetitorBase K q 1 profile ambientBase ^ k := by
  exact cwTotalWeightInnerHashModulus_cast_le
    K q (data.exponent k) profile hprofileMass k hk
    (data.length_eq k hk) (data.coarseWord k) (data.coarse_type k hk)
    ambientBase data.ambientBase_nonneg ambientLoss (data.ambientLoss_pos k)
    (data.ambient_upper k hk)

/-- The exact marked target family has the pushed-profile target base uniformly over the coarse
representative sequence. -/
theorem targetBase_pow_le_markedFiber
    (data : CWTotalWeightInnerGrowthData K q profile ambientBase ambientLoss)
    (hprofileMass : 0 < WordType.profileMass profile)
    (k : ℕ) (hk : 0 < k) :
    cwTotalWeightInnerTargetBase K q 1 profile ^ k ≤
      WordType.pushedTypeFiberLoss profile k *
        ((cwTotalWeightMarkedFiberWords K q 1 (data.exponent k)
          (WordType.proportionalCounts profile k) (data.coarseWord k)).card : ℝ) := by
  exact cwTotalWeightInnerTargetBase_pow_le_markedFiber
    K q 1 (data.exponent k) profile hprofileMass k hk
      (data.length_eq k hk) (data.coarseWord k) (data.coarse_type k hk)

end CWTotalWeightInnerGrowthData

/-- Choose the standard half-interval Behrend buckets and run the already-proved finite marked
hashing extraction.  This is the exact finite datum from which a sequence client chooses its
inner copy count; the displayed inequality contains the full `M²` affine-hashing denominator and
the bucket cardinality is literally `rothNumberNat (M/2)`. -/
theorem exists_cwTotalWeightInnerPrimeBehrendExtraction
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    ∃ B : Finset (CWTotalWeightInnerHashField K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord),
      B.card = rothNumberNat
        (cwTotalWeightInnerHashModulus K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord / 2) ∧
      ThreeAPFree (B : Set (CWTotalWeightInnerHashField K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)) ∧
      ∃ seed : ProgressionHash.Seed
          (CWTotalWeightInnerHashField K q n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord)
          (Fin (n + 1)),
        3 * (cwTotalWeightMarkedFiberWords K q 1 n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord).card * B.card ≤
          4 * (cwTotalWeightInnerHashModulus K q n
              (WordType.proportionalCounts leaf.profile.count k) coarseWord *
            cwTotalWeightInnerHashModulus K q n
              (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
            ((cwTotalWeightInnerPartitionHashEncoding K q n
              (WordType.proportionalCounts leaf.profile.count k) coarseWord
              ).markedLegwiseIsolatedPowerAddresses n
                (cwTotalWeightLocalizedAmbientWords K q 1 n
                  (WordType.proportionalCounts leaf.profile.count k) coarseWord)
                (cwTotalWeightMarkedFiberWords K q 1 n
                  (WordType.proportionalCounts leaf.profile.count k) coarseWord)
                B seed).card ∧
        PolynomialDegenerates
          (cwTotalWeightLocalizedFineTypes K q 1 n
            (positiveSupportWordBlockAddress
              (CWTotalWeightCoarseSupport K q 1) n coarseWord)
            (cwTotalWeightFineMarginalType K q 1
              (WordType.proportionalCounts leaf.profile.count k))).realize
          (Tensor.indexedDirectSum
            (fun _selected : (cwTotalWeightInnerPartitionHashEncoding K q n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord
                ).markedLegwiseIsolatedPowerAddresses n
                  (cwTotalWeightLocalizedAmbientWords K q 1 n
                    (WordType.proportionalCounts leaf.profile.count k) coarseWord)
                  (cwTotalWeightMarkedFiberWords K q 1 n
                    (WordType.proportionalCounts leaf.profile.count k) coarseWord)
                  B seed ↦
              matrixMultiplication (K := K)
                (leaf.dimensionProduct .X ^ k)
                (leaf.dimensionProduct .Y ^ k)
                (leaf.dimensionProduct .Z ^ k))) := by
  let M := cwTotalWeightInnerHashModulus K q n
    (WordType.proportionalCounts leaf.profile.count k) coarseWord
  obtain ⟨B, hBcard, hBfree⟩ := exists_threeAPFree_zmod_half M
  obtain ⟨seed, hcount, hdegenerates⟩ :=
    exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSum
      K q leaf hdimension n k coarseWord B hBfree
  refine ⟨B, ?_, hBfree, seed, ?_, hdegenerates⟩
  · exact hBcard
  · simpa only [CWTotalWeightInnerHashField, ZMod.card,
      cwTotalWeightInnerHashModulus] using hcount

/-! ## Canonical chosen finite sequence -/

/-- Canonical half-interval Behrend bucket set in the safe inner prime field. -/
noncomputable def cwTotalWeightInnerBehrendBuckets
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    Finset (CWTotalWeightInnerHashField K q n profile coarseWord) :=
  Classical.choose (exists_threeAPFree_zmod_half
    (cwTotalWeightInnerHashModulus K q n profile coarseWord))

theorem cwTotalWeightInnerBehrendBuckets_card
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    (cwTotalWeightInnerBehrendBuckets K q n profile coarseWord).card =
      rothNumberNat
        (cwTotalWeightInnerHashModulus K q n profile coarseWord / 2) :=
  (Classical.choose_spec (exists_threeAPFree_zmod_half
    (cwTotalWeightInnerHashModulus K q n profile coarseWord))).1

theorem cwTotalWeightInnerBehrendBuckets_threeAPFree
    (K : Type u) [CommRing K] (q n : ℕ)
    (profile : (cwChunkPartitionedTensor K q 1).support → ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    ThreeAPFree
      (cwTotalWeightInnerBehrendBuckets K q n profile coarseWord :
        Set (CWTotalWeightInnerHashField K q n profile coarseWord)) :=
  (Classical.choose_spec (exists_threeAPFree_zmod_half
    (cwTotalWeightInnerHashModulus K q n profile coarseWord))).2

/-- Canonical good affine seed for the standard bucket choice. -/
noncomputable def cwTotalWeightInnerBehrendSeed
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    ProgressionHash.Seed
      (CWTotalWeightInnerHashField K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)
      (Fin (n + 1)) :=
  Classical.choose
    (exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSum
      K q leaf hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBuckets K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)
      (cwTotalWeightInnerBehrendBuckets_threeAPFree K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord))

/-- Canonical inner copy count after localized marked hashing. -/
noncomputable def cwTotalWeightInnerBehrendCopies
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) : ℕ :=
  ((cwTotalWeightInnerPartitionHashEncoding K q n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord
      ).markedLegwiseIsolatedPowerAddresses n
        (cwTotalWeightLocalizedAmbientWords K q 1 n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightMarkedFiberWords K q 1 n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightInnerBehrendBuckets K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightInnerBehrendSeed K q leaf hdimension n k coarseWord)).card

/-- The naturally indexed selected-address type whose cardinality is the canonical inner copy
count.  Exposing this type avoids replacing the full extracted family by a representative leaf
when constructing a nested laser sequence. -/
noncomputable abbrev CWTotalWeightInnerBehrendIndex
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :=
  (cwTotalWeightInnerPartitionHashEncoding K q n
      (WordType.proportionalCounts leaf.profile.count k) coarseWord
      ).markedLegwiseIsolatedPowerAddresses n
        (cwTotalWeightLocalizedAmbientWords K q 1 n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightMarkedFiberWords K q 1 n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightInnerBehrendBuckets K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord)
        (cwTotalWeightInnerBehrendSeed K q leaf hdimension n k coarseWord)

@[simp] theorem card_cwTotalWeightInnerBehrendIndex
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
      Fintype.card (CWTotalWeightInnerBehrendIndex
      K q leaf hdimension n k coarseWord) =
      cwTotalWeightInnerBehrendCopies K q leaf hdimension n k coarseWord := by
  exact Fintype.card_coe _

/-- Exact hashing count for the canonical choices. -/
theorem cwTotalWeightInnerBehrend_hashCount
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    3 * (cwTotalWeightMarkedFiberWords K q 1 n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord).card *
        rothNumberNat (cwTotalWeightInnerHashModulus K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord / 2) ≤
      4 * (cwTotalWeightInnerHashModulus K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord *
        cwTotalWeightInnerHashModulus K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
        cwTotalWeightInnerBehrendCopies K q leaf hdimension n k coarseWord := by
  have hspec := (Classical.choose_spec
    (exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSum
      K q leaf hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBuckets K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)
      (cwTotalWeightInnerBehrendBuckets_threeAPFree K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord))).1
  calc
    3 * (cwTotalWeightMarkedFiberWords K q 1 n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card *
        rothNumberNat (cwTotalWeightInnerHashModulus K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord / 2) =
      3 * (cwTotalWeightMarkedFiberWords K q 1 n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card *
        (cwTotalWeightInnerBehrendBuckets K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord).card := by
      rw [cwTotalWeightInnerBehrendBuckets_card]
    _ ≤ 4 * (Fintype.card (CWTotalWeightInnerHashField K q n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
          Fintype.card (CWTotalWeightInnerHashField K q n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord)) *
        cwTotalWeightInnerBehrendCopies K q leaf hdimension n k coarseWord := by
      simpa only [cwTotalWeightInnerBehrendSeed,
        cwTotalWeightInnerBehrendCopies] using hspec
    _ = 4 * (cwTotalWeightInnerHashModulus K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord *
        cwTotalWeightInnerHashModulus K q n
          (WordType.proportionalCounts leaf.profile.count k) coarseWord) *
        cwTotalWeightInnerBehrendCopies K q leaf hdimension n k coarseWord := by
      simp only [CWTotalWeightInnerHashField, ZMod.card,
        cwTotalWeightInnerHashModulus]

/-- Exact tensor degeneration for the canonical inner-copy sequence. -/
theorem cwTotalWeightInnerBehrend_degenerates
    (K : Type u) [CommRing K] (q : ℕ)
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (n k : ℕ)
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q 1) n) :
    PolynomialDegenerates
      (cwTotalWeightLocalizedFineTypes K q 1 n
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q 1) n coarseWord)
        (cwTotalWeightFineMarginalType K q 1
          (WordType.proportionalCounts leaf.profile.count k))).realize
      (Tensor.indexedDirectSum
        (fun _selected : (cwTotalWeightInnerPartitionHashEncoding K q n
            (WordType.proportionalCounts leaf.profile.count k) coarseWord
            ).markedLegwiseIsolatedPowerAddresses n
              (cwTotalWeightLocalizedAmbientWords K q 1 n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              (cwTotalWeightMarkedFiberWords K q 1 n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              (cwTotalWeightInnerBehrendBuckets K q n
                (WordType.proportionalCounts leaf.profile.count k) coarseWord)
              (cwTotalWeightInnerBehrendSeed K q leaf hdimension n k coarseWord) ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) := by
  exact (Classical.choose_spec
    (exists_seed_many_cwTotalWeightInnerPrimeMarkedLeafDirectSum
      K q leaf hdimension n k coarseWord
      (cwTotalWeightInnerBehrendBuckets K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord)
      (cwTotalWeightInnerBehrendBuckets_threeAPFree K q n
        (WordType.proportionalCounts leaf.profile.count k) coarseWord))).2

namespace CWTotalWeightInnerGrowthData

/-- Every base strictly below the exact target/field quotient (allowing an arbitrarily small
temporary factor `δ > 1` to absorb the subexponential prime loss) is eventually attained by the
canonical Behrend copy sequence.

This theorem is the complete asymptotic counting conclusion of the localized inner extraction.
The tensor degeneration of those same copies is
`cwTotalWeightInnerBehrend_degenerates`. -/
theorem exists_eventually_pow_le_behrendCopies
    {K : Type u} [CommRing K] {q : ℕ}
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthData K q leaf.profile.count
      ambientBase ambientLoss)
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W < cwTotalWeightInnerTargetBase K q 1 leaf.profile.count /
      (δ * cwTotalWeightInnerCompetitorBase K q 1 leaf.profile.count ambientBase)) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → 0 < k →
      W ^ k ≤
        (cwTotalWeightInnerBehrendCopies K q leaf hdimension
          (data.exponent k) k (data.coarseWord k) : ℝ) := by
  letI : Nonempty (cwChunkPartitionedTensor K q 1).support :=
    ⟨cwChunkSupportWitness K q 1⟩
  let targetBase := cwTotalWeightInnerTargetBase K q 1 leaf.profile.count
  let fieldBase := cwTotalWeightInnerCompetitorBase K q 1 leaf.profile.count ambientBase
  let enlargedFieldBase := δ * fieldBase
  let targetLoss := WordType.pushedTypeFiberLoss leaf.profile.count
  let poly : ℕ → ℝ := fun k ↦ 4 * targetLoss k
  have hfieldBase : 0 < fieldBase := by
    exact zero_lt_one.trans_le
      (one_le_cwTotalWeightInnerCompetitorBase K q 1 leaf.profile.count ambientBase)
  have henlargedFieldBase : 0 < enlargedFieldBase := by
    exact mul_pos (zero_lt_one.trans hδ) hfieldBase
  have hpoly : Growth.Subexponential poly := by
    exact (WordType.pushedTypeFiberLoss_subexponential leaf.profile.count).const_mul
      (by norm_num : (0 : ℝ) ≤ 4)
  obtain ⟨Nfield, hNfield⟩ := data.fieldLoss_subexponential.eventually_le_pow hδ
  obtain ⟨Nrate, hNrate⟩ := Growth.exists_forall_pow_le_copies
    henlargedFieldBase (by norm_num : (0 : ℝ) < 1) hpoly hW
    (by simpa only [targetBase, enlargedFieldBase] using hWrate)
  refine ⟨max Nfield Nrate, fun k hk hkpos ↦ ?_⟩
  have hkField : Nfield ≤ k := (Nat.le_max_left _ _).trans hk
  have hkRate : Nrate ≤ k := (Nat.le_max_right _ _).trans hk
  let M := data.modulus k
  let copies := cwTotalWeightInnerBehrendCopies K q leaf hdimension
    (data.exponent k) k (data.coarseWord k)
  have hMtwo : 2 ≤ M := by
    have hchar := PrimeFieldSizing.characteristicFloor_lt_modulus 9 (data.requirement k)
    dsimp [M, CWTotalWeightInnerGrowthData.modulus]
    omega
  have hMsharp : (M : ℝ) ≤ data.fieldLoss k * fieldBase ^ k := by
    simpa only [M, fieldBase] using
      data.modulus_cast_le_fieldLoss_mul_pow leaf.profile.mass_pos k hkpos
  have hMupper : (M : ℝ) ≤ 1 * enlargedFieldBase ^ k := by
    calc
      (M : ℝ) ≤ data.fieldLoss k * fieldBase ^ k := hMsharp
      _ ≤ δ ^ k * fieldBase ^ k :=
        mul_le_mul_of_nonneg_right (hNfield k hkField)
          (pow_nonneg hfieldBase.le k)
      _ = 1 * enlargedFieldBase ^ k := by
        rw [one_mul, mul_pow]
  have htarget := data.targetBase_pow_le_markedFiber
    leaf.profile.mass_pos k hkpos
  let marked := (cwTotalWeightMarkedFiberWords K q 1 (data.exponent k)
    (WordType.proportionalCounts leaf.profile.count k) (data.coarseWord k)).card
  have htarget' : targetBase ^ k ≤ targetLoss k * (marked : ℝ) := by
    simpa only [targetBase, targetLoss, marked] using htarget
  have hhashNat := cwTotalWeightInnerBehrend_hashCount
    K q leaf hdimension (data.exponent k) k (data.coarseWord k)
  have hhash : 3 * (marked : ℝ) * (rothNumberNat (M / 2) : ℝ) ≤
      4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
    exact_mod_cast hhashNat
  have hcount : targetBase ^ k * (rothNumberNat (M / 2) : ℝ) ≤
      poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
    calc
      targetBase ^ k * (rothNumberNat (M / 2) : ℝ) ≤
          (targetLoss k * (marked : ℝ)) *
            (rothNumberNat (M / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right htarget' (by positivity)
      _ ≤ targetLoss k *
          (3 * (marked : ℝ) * (rothNumberNat (M / 2) : ℝ)) := by
        have htargetLoss : 0 ≤ targetLoss k :=
          (WordType.pushedTypeFiberLoss_pos leaf.profile.count k).le
        have hmarkedRoth : 0 ≤ (marked : ℝ) *
            (rothNumberNat (M / 2) : ℝ) := by positivity
        nlinarith
      _ ≤ targetLoss k *
          (4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ)) :=
        mul_le_mul_of_nonneg_left hhash
          (WordType.pushedTypeFiberLoss_pos leaf.profile.count k).le
      _ = poly k * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
        unfold poly
        ring
  exact hNrate k M copies hkRate hMtwo hMupper hcount

/-- The canonical selected-address family is nonempty at every positive proportional
repetition.  This is not an additional certificate premise: positivity follows from the exact
target-fiber lower bound, positivity of the half-interval Roth number, and the canonical hashing
count inequality. -/
theorem behrendCopies_pos
    {K : Type u} [CommRing K] {q : ℕ}
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthData K q leaf.profile.count
      ambientBase ambientLoss)
    (k : ℕ) (hk : 0 < k) :
    0 < cwTotalWeightInnerBehrendCopies K q leaf hdimension
      (data.exponent k) k (data.coarseWord k) := by
  letI : Nonempty (cwChunkPartitionedTensor K q 1).support :=
    ⟨cwChunkSupportWitness K q 1⟩
  let M := data.modulus k
  let marked := (cwTotalWeightMarkedFiberWords K q 1 (data.exponent k)
    (WordType.proportionalCounts leaf.profile.count k) (data.coarseWord k)).card
  let copies := cwTotalWeightInnerBehrendCopies K q leaf hdimension
    (data.exponent k) k (data.coarseWord k)
  have hM : 9 < M := by
    simpa only [M, CWTotalWeightInnerGrowthData.modulus] using
      PrimeFieldSizing.characteristicFloor_lt_modulus 9 (data.requirement k)
  have hhalf : 0 < M / 2 := by omega
  have htarget := data.targetBase_pow_le_markedFiber
    leaf.profile.mass_pos k hk
  have htarget' :
      cwTotalWeightInnerTargetBase K q 1 leaf.profile.count ^ k ≤
        WordType.pushedTypeFiberLoss leaf.profile.count k * (marked : ℝ) := by
    simpa only [marked] using htarget
  have htargetPos :
      0 < cwTotalWeightInnerTargetBase K q 1 leaf.profile.count ^ k :=
    pow_pos (cwTotalWeightInnerTargetBase_pos K q 1 leaf.profile.count) k
  have hmarked : 0 < marked := by
    by_contra hnot
    have hzero : marked = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, Nat.cast_zero, mul_zero] at htarget'
    exact (not_lt_of_ge htarget') htargetPos
  have hroth : 0 < rothNumberNat (M / 2) := rothNumberNat_pos hhalf
  have hhash : 3 * marked * rothNumberNat (M / 2) ≤ 4 * (M * M) * copies := by
    simpa only [M, marked, copies, CWTotalWeightInnerGrowthData.modulus,
      CWTotalWeightInnerGrowthData.requirement, cwTotalWeightInnerHashModulus] using
      cwTotalWeightInnerBehrend_hashCount
        K q leaf hdimension (data.exponent k) k (data.coarseWord k)
  have hcopies : 0 < copies := by
    by_contra hnot
    have hzero : copies = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, Nat.mul_zero] at hhash
    have hleft : 0 < 3 * marked * rothNumberNat (M / 2) := by positivity
    omega
  exact hcopies

/-- Sequence-ready count growth for the canonical inner extraction.

The returned loss absorbs the finite prefix before the Behrend rate theorem applies.  Thus the
inequality holds at every positive repetition, exactly in the form required by
`CanonicalInnerSequenceData.inner_copy_growth`, and the tensor-power stride is unchanged. -/
theorem exists_subexponentialLoss_pow_le_behrendCopies
    {K : Type u} [CommRing K] {q : ℕ}
    {C : Leg → Type*} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    {ambientBase : ℝ} {ambientLoss : ℕ → ℝ}
    (data : CWTotalWeightInnerGrowthData K q leaf.profile.count
      ambientBase ambientLoss)
    {δ W : ℝ} (hδ : 1 < δ) (hW : 0 < W)
    (hWrate : W < cwTotalWeightInnerTargetBase K q 1 leaf.profile.count /
      (δ * cwTotalWeightInnerCompetitorBase K q 1 leaf.profile.count ambientBase)) :
    ∃ loss : ℕ → ℝ,
      Growth.Subexponential loss ∧
      (∀ k, 0 < loss k) ∧
      ∀ k, 0 < k →
        W ^ k ≤ loss k *
          (cwTotalWeightInnerBehrendCopies K q leaf hdimension
            (data.exponent k) k (data.coarseWord k) : ℝ) := by
  obtain ⟨N, hN⟩ := data.exists_eventually_pow_le_behrendCopies
    leaf hdimension hδ hW hWrate
  refine ⟨Growth.finitePrefixPowerLoss W N,
    Growth.finitePrefixPowerLoss_subexponential hW.le N,
    fun k ↦ Growth.finitePrefixPowerLoss_pos hW N k, ?_⟩
  exact Growth.pow_le_finitePrefixPowerLoss_mul_count hW
    (fun k hk ↦ data.behrendCopies_pos leaf hdimension k hk) hN

end CWTotalWeightInnerGrowthData

end AlgebraicComplexity.Examples
