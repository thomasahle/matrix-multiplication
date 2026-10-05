/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryProductProjectionProfile
import AlgebraicComplexity.Combinatorics.PooledMarginalTypeConcentrationSource
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInputHoles
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetCounting

set_option autoImplicit false

/-!
# Concentration of recursive CW input-profile holes

An exact recursive target label consists of two labelled child split words at every parent
position.  This module pairs those words without changing their order and applies the pooled
information-projection tail bound.  The finite theorem exposes only four semantic identities:

* the exact doubled tagged-cell word carried by the reference quotient;
* the exact ordered-state type of that quotient;
* the exact pooled labelled-occurrence table of the child target; and
* equality of the complementary-product reference parent law with the selected parent
  complete-split law.

Everything else is derived: the native parent-label encoding is injective, exact target
membership implies pooled feasibility (including structural zeroes), failure of the approximate
parent selector implies a parent-profile deviation, and the input-hole set injects into the
generic exponentially small tail.

No compatibility cleanup count, repair theorem, tensor degeneration, asymptotic limit, or
certificate-specific numerical inequality occurs here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-! ## Pair the two labelled child halves -/

/-- The two complete-split child words carried by one native recursive parent position. -/
noncomputable def cwRecursivePairedChildSplitWord
    (depth n : ℕ)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    Fin (n + 1) → SplitWord depth × SplitWord depth :=
  let children := cwRecursiveLabelledChildrenEquiv depth n parent
  fun sample ↦
    (children (Fin.castAdd (n + 1) sample),
      children (Fin.natAdd (n + 1) sample))

@[simp] theorem cwRecursivePairedChildSplitWord_fst
    (depth n : ℕ)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (sample : Fin (n + 1)) :
    (cwRecursivePairedChildSplitWord depth n parent sample).1 =
      cwRecursiveLabelledChildrenEquiv depth n parent
        (Fin.castAdd (n + 1) sample) :=
  rfl

@[simp] theorem cwRecursivePairedChildSplitWord_snd
    (depth n : ℕ)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (sample : Fin (n + 1)) :
    (cwRecursivePairedChildSplitWord depth n parent sample).2 =
      cwRecursiveLabelledChildrenEquiv depth n parent
        (Fin.natAdd (n + 1) sample) :=
  rfl

/-- Pairing the labelled child halves loses no native parent label. -/
theorem cwRecursivePairedChildSplitWord_injective (depth n : ℕ) :
    Function.Injective (cwRecursivePairedChildSplitWord depth n) := by
  intro left right hpairs
  apply (cwRecursiveLabelledChildrenEquiv depth n).injective
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · exact congrArg Prod.fst (congrFun hpairs sample)
  · exact congrArg Prod.snd (congrFun hpairs sample)

/-- Joining the paired children recovers the complete-split encoding of the native parent
chunk at that position. -/
theorem concat_cwRecursivePairedChildSplitWord
    (depth n : ℕ)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (sample : Fin (n + 1)) :
    concatSplitWords
        (cwRecursivePairedChildSplitWord depth n parent sample).1
        (cwRecursivePairedChildSplitWord depth n parent sample).2 =
      cwChunkSplitWord (depth + 1)
        (positiveWordEquiv _ n parent sample) := by
  apply (splitWordSuccEquiv depth).injective
  rw [splitWordSuccEquiv_concatSplitWords]
  apply Prod.ext
  · simp only [cwRecursivePairedChildSplitWord_fst,
      cwRecursiveLabelledChildrenEquiv_apply,
      positiveWordLabelledChildren_left,
      leftChildHalf_eq_splitWordSuccEquiv]
  · simp only [cwRecursivePairedChildSplitWord_snd,
      cwRecursiveLabelledChildrenEquiv_apply,
      positiveWordLabelledChildren_right,
      rightChildHalf_eq_splitWordSuccEquiv]

/-! ## Exact target labels are pooled-feasible -/

/-- Exact recursive target membership supplies the pooled-profile predicate for the paired
parent word.

`hsourceCells` identifies the target's doubled tagged-cell word with the left state cells followed
by the complementary right state cells.  `hstateReference` and `htargetReference` are literal
normalized finite-table equalities; structural-zero support is derived by the generic projection
adapter. -/
theorem cwRecursiveExactTarget_isPooledMarginalProfile
    {State : Type u} [Fintype State] [DecidableEq State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (logicalLeg : Leg)
    (M : ComplementaryProductProjectionModel State
      (CWOrientedCoarseCell Part depth) (SplitWord depth))
    (state : Fin (n + 1) → State)
    (hsourceCells :
      cwRecursiveOrientedFiniteCellSequence
          depth n partAt sigma reference =
        Fin.append (M.cellOf ∘ state)
          (M.cellOf ∘ M.complement ∘ state))
    (hstateReference : ∀ u,
      (WordType.multiplicity state u : ℝ) / (n + 1) =
        M.stateLaw.weight u)
    (htargetReference : ∀ cell word,
      (targets.exactProfile logicalLeg
          (cwOrientedCoarseCellToIndex cell) word : ℝ) / (n + 1) =
        (M.reference.pushforward M.leftFeature).weight (cell, word) +
          (M.reference.pushforward M.rightFeature).weight (cell, word))
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (hparent : parent ∈ cwRecursiveExactTargetFiberParts
      partAt sigma targets reference (sigma logicalLeg)) :
    WordType.IsPooledMarginalProfile
      M.toSparsePooledMarginalProjectionModel
      (WordType.multiplicity
        (ComplementaryOccurrenceLaw.parentPairWord state
          (fun sample ↦
            (cwRecursivePairedChildSplitWord depth n parent sample).1)
          (fun sample ↦
            (cwRecursivePairedChildSplitWord depth n parent sample).2))) := by
  classical
  let children := cwRecursiveLabelledChildrenEquiv depth n parent
  let left : Fin (n + 1) → SplitWord depth := fun sample ↦
    children (Fin.castAdd (n + 1) sample)
  let right : Fin (n + 1) → SplitWord depth := fun sample ↦
    children (Fin.natAdd (n + 1) sample)
  let profile := WordType.multiplicity
    (ComplementaryOccurrenceLaw.parentPairWord state left right)
  have hjoint := WordType.mem_conditionalTypeClass.mp
    ((mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
      partAt sigma targets hsupported hcoarseSupported reference logicalLeg parent).mp hparent)
  have hprofileMass : WordType.profileMass profile = n + 1 := by
    rw [WordType.profileMass, WordType.sum_multiplicity]
  apply M.isPooledMarginalProfile_of_normalized_marginals profile
  · rw [hprofileMass]
    exact Nat.zero_lt_succ n
  · intro u
    change (WordType.mappedType Prod.fst profile u : ℝ) /
        WordType.profileMass profile = M.stateLaw.weight u
    rw [ComplementaryOccurrenceLaw.mappedType_fst_multiplicity_parentPairWord,
      hprofileMass]
    simpa only [Nat.cast_add, Nat.cast_one] using hstateReference u
  · rintro ⟨cell, word⟩
    rw [← add_div]
    rw [← Nat.cast_add]
    rw [M.pooledMappedType_parentPairWord_eq_labelledCellWord state left right]
    have hword :
        Fin.append
            (fun i ↦ (M.cellOf (state i), left i))
            (fun i ↦ (M.cellOf (M.complement (state i)), right i)) =
          WordType.jointWord
            (cwRecursiveOrientedFiniteCellSequence
              depth n partAt sigma reference) children := by
      funext occurrence
      refine Fin.addCases ?_ ?_ occurrence <;> intro sample
      · have hcell := congrFun hsourceCells
          (Fin.castAdd (n + 1) sample)
        apply Prod.ext
        · simpa only [Fin.append_left, WordType.jointWord,
            Function.comp_apply] using hcell.symm
        · simp only [Fin.append_left, WordType.jointWord, left, children]
      · have hcell := congrFun hsourceCells
          (Fin.natAdd (n + 1) sample)
        apply Prod.ext
        · simpa only [Fin.append_right, WordType.jointWord,
            Function.comp_apply] using hcell.symm
        · simp only [Fin.append_right, WordType.jointWord, right, children]
    rw [hword, hjoint, hprofileMass]
    simpa only [Nat.cast_add, Nat.cast_one] using htargetReference cell word

/-! ## Missing the approximate parent selector gives a deviation -/

/-- An exact target label rejected by the approximate parent selector has a coordinatewise
parent-profile deviation for the complementary-product reference.

The equality `hparentReference` is the precise complete-split recursion boundary: joining the two
reference child symbols must give the semantic parent law selected at the input. -/
theorem cwRecursiveExactTarget_hasParentDeviation_of_not_approximatelyMatches
    {State : Type u} [Fintype State] [DecidableEq State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (logicalLeg : Leg)
    (M : ComplementaryProductProjectionModel State
      (CWOrientedCoarseCell Part depth) (SplitWord depth))
    (state : Fin (n + 1) → State)
    (hparentReference :
      M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2) =
        ((cwRecursiveSemanticParentTerm term hmultiplicity).split
          (sigma logicalLeg)).probability)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (hparent : parent ∈ cwRecursiveExactTargetFiberParts
      partAt sigma targets reference (sigma logicalLeg))
    (hnot : ¬ cwRecursiveParentLabelApproximatelyMatches
      term hmultiplicity epsilon (sigma logicalLeg) parent) :
    WordType.PooledParentProfileHasDeviation
      M.toSparsePooledMarginalProjectionModel
      (fun sample ↦ concatSplitWords sample.2.1 sample.2.2)
      (WordType.multiplicity
        (ComplementaryOccurrenceLaw.parentPairWord state
          (fun sample ↦
            (cwRecursivePairedChildSplitWord depth n parent sample).1)
          (fun sample ↦
            (cwRecursivePairedChildSplitWord depth n parent sample).2)))
      epsilon := by
  classical
  let left : Fin (n + 1) → SplitWord depth := fun sample ↦
    (cwRecursivePairedChildSplitWord depth n parent sample).1
  let right : Fin (n + 1) → SplitWord depth := fun sample ↦
    (cwRecursivePairedChildSplitWord depth n parent sample).2
  let pairs := ComplementaryOccurrenceLaw.parentPairWord state left right
  let parentSequence : Fin (n + 1) → SplitWord (depth + 1) :=
    fun sample ↦ concatSplitWords (left sample) (right sample)
  let beta := (cwRecursiveSemanticParentTerm term hmultiplicity).split
    (sigma logicalLeg)
  have hsequence : parentSequence =
      cwChunkSplitWord (depth + 1) ∘
        positiveWordEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n parent := by
    funext sample
    exact concat_cwRecursivePairedChildSplitWord depth n parent sample
  have hgroup : cwRecursiveLabelledChildWord depth n parent =
      reference (sigma logicalLeg) :=
    (mem_cwRecursiveExactTargetFiberParts_iff
      partAt sigma targets reference (sigma logicalLeg) parent).mp hparent |>.1
  have hsupported : ∀ sample,
      splitWordWeight (parentSequence sample) = term.index.count (sigma logicalLeg) := by
    intro sample
    change splitWordWeight (concatSplitWords (left sample) (right sample)) = _
    rw [splitWordWeight_concatSplitWords]
    calc
      splitWordWeight (left sample) + splitWordWeight (right sample) =
          (cwRecursiveLabelledChildWord depth n parent
              (Fin.castAdd (n + 1) sample) : ℕ) +
            (cwRecursiveLabelledChildWord depth n parent
              (Fin.natAdd (n + 1) sample) : ℕ) := by
        rw [val_cwRecursiveLabelledChildWord_eq_splitWordWeight,
          val_cwRecursiveLabelledChildWord_eq_splitWordWeight]
        rfl
      _ = (reference (sigma logicalLeg) (Fin.castAdd (n + 1) sample) : ℕ) +
            (reference (sigma logicalLeg) (Fin.natAdd (n + 1) sample) : ℕ) := by
        rw [hgroup]
      _ = term.index.count (sigma logicalLeg) :=
        cwRecursiveRelaxedAmbientCoarseSupport_left_add_right
          term sigma alpha reference hreference (sigma logicalLeg) sample
  have hnotSequence : ¬ beta.MatchesSequenceApproximately parentSequence epsilon := by
    change ¬ beta.MatchesSequenceApproximately
      (cwChunkSplitWord (depth + 1) ∘
        positiveWordEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n parent) epsilon at hnot
    simpa only [hsequence] using hnot
  have hnotClose : ¬ ∀ word,
      |(WordType.multiplicity parentSequence word : ℝ) / (n + 1) -
          beta.weight word| ≤ epsilon := by
    intro hclose
    exact hnotSequence ⟨by
      intro sample
      simpa [beta, cwRecursiveSemanticParentTerm_index] using hsupported sample,
      by simpa only [Nat.cast_add, Nat.cast_one] using hclose⟩
  push Not at hnotClose
  obtain ⟨word, hword⟩ := hnotClose
  refine ⟨word, ?_⟩
  have hprofileMass :
      WordType.profileMass (WordType.multiplicity pairs) = n + 1 := by
    rw [WordType.profileMass, WordType.sum_multiplicity]
  have hparentType :
      WordType.mappedType
          (fun sample : State × (SplitWord depth × SplitWord depth) ↦
            concatSplitWords sample.2.1 sample.2.2)
          (WordType.multiplicity pairs) =
        WordType.multiplicity parentSequence := by
    rw [← WordType.multiplicity_comp_eq_mappedType]
    rfl
  change epsilon ≤
    |(WordType.mappedType
          (fun sample : State × (SplitWord depth × SplitWord depth) ↦
            concatSplitWords sample.2.1 sample.2.2)
          (WordType.multiplicity pairs) word : ℝ) /
        WordType.profileMass (WordType.multiplicity pairs) -
      (M.reference.pushforward
        (fun sample : State × (SplitWord depth × SplitWord depth) ↦
          concatSplitWords sample.2.1 sample.2.2)).weight word|
  rw [hprofileMass, hparentType]
  have href :
      M.reference.pushforward
          (fun sample : State × (SplitWord depth × SplitWord depth) ↦
            concatSplitWords sample.2.1 sample.2.2) =
        beta.probability := by
    change M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2) =
      beta.probability
    simpa only [beta] using hparentReference
  rw [href]
  simpa only [CompleteSplitDistribution.weight,
    Nat.cast_add, Nat.cast_one] using hword.le

/-! ## Finite input-hole tail -/

/-- The recursive input-profile holes inject into the generic pooled-marginal deviation set.
All four semantic-identity hypotheses are uniform in the target label. -/
theorem card_cwRecursiveInputProfileHoles_le_pooledMarginalDeviatingWords
    {State : Type u} [Fintype State] [DecidableEq State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (logicalLeg : Leg)
    (M : ComplementaryProductProjectionModel State
      (CWOrientedCoarseCell Part depth) (SplitWord depth))
    (state : Fin (n + 1) → State)
    (hsourceCells :
      cwRecursiveOrientedFiniteCellSequence
          depth n partAt sigma reference =
        Fin.append (M.cellOf ∘ state)
          (M.cellOf ∘ M.complement ∘ state))
    (hstateReference : ∀ u,
      (WordType.multiplicity state u : ℝ) / (n + 1) =
        M.stateLaw.weight u)
    (htargetReference : ∀ cell word,
      (targets.exactProfile logicalLeg
          (cwOrientedCoarseCellToIndex cell) word : ℝ) / (n + 1) =
        (M.reference.pushforward M.leftFeature).weight (cell, word) +
          (M.reference.pushforward M.rightFeature).weight (cell, word))
    (hparentReference :
      M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2) =
        ((cwRecursiveSemanticParentTerm term hmultiplicity).split
          (sigma logicalLeg)).probability) :
    (cwRecursiveInputProfileHoles
        partAt sigma term hmultiplicity epsilon targets reference
          (sigma logicalLeg)).card ≤
      (WordType.pooledMarginalDeviatingWordsForSource
        M.toSparsePooledMarginalProjectionModel
        (fun sample ↦ concatSplitWords sample.2.1 sample.2.2)
        state epsilon).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (cwRecursivePairedChildSplitWord depth n)
  · intro parent hparentHole
    have hhole := (mem_cwRecursiveInputProfileHoles_iff
      partAt sigma term hmultiplicity epsilon targets reference
        (sigma logicalLeg) parent).mp hparentHole
    apply (WordType.mem_pooledMarginalDeviatingWordsForSource
      M.toSparsePooledMarginalProjectionModel
      (fun sample ↦ concatSplitWords sample.2.1 sample.2.2)
      state epsilon (cwRecursivePairedChildSplitWord depth n parent)).mpr
    constructor
    · exact cwRecursiveExactTarget_isPooledMarginalProfile
        partAt sigma targets hsupported hcoarseSupported reference logicalLeg
          M state hsourceCells hstateReference htargetReference parent hhole.1
    · exact cwRecursiveExactTarget_hasParentDeviation_of_not_approximatelyMatches
        partAt sigma term hmultiplicity epsilon alpha targets reference hreference
          logicalLeg M state hparentReference parent hhole.1 hhole.2
  · intro left _ right _ heq
    exact cwRecursivePairedChildSplitWord_injective depth n heq

/-- **Finite recursive input-hole concentration.**  Under the four exact semantic
identities, the number of target labels omitted by the approximate parent selector has the
literal method-of-types upper bound with entropy loss `epsilon^2 / 4` per parent position.

The source profile may have structural zeroes.  The only scaling assumption is the exact
multiplicity equality of the ordered-state word. -/
theorem card_cwRecursiveInputProfileHoles_le
    {State : Type u} [Fintype State] [DecidableEq State]
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (hreference : reference ∈
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha)
    (logicalLeg : Leg)
    (M : ComplementaryProductProjectionModel State
      (CWOrientedCoarseCell Part depth) (SplitWord depth))
    (state : Fin (n + 1) → State)
    (sourceProfile : State → ℕ) (hmass : 0 < WordType.profileMass sourceProfile)
    (k : ℕ) (hk : 0 < k)
    (hsource : WordType.multiplicity state =
      WordType.proportionalCounts sourceProfile k)
    (hsourceCells :
      cwRecursiveOrientedFiniteCellSequence
          depth n partAt sigma reference =
        Fin.append (M.cellOf ∘ state)
          (M.cellOf ∘ M.complement ∘ state))
    (hstateReference : ∀ u,
      (WordType.multiplicity state u : ℝ) / (n + 1) =
        M.stateLaw.weight u)
    (htargetReference : ∀ cell word,
      (targets.exactProfile logicalLeg
          (cwOrientedCoarseCellToIndex cell) word : ℝ) / (n + 1) =
        (M.reference.pushforward M.leftFeature).weight (cell, word) +
          (M.reference.pushforward M.rightFeature).weight (cell, word))
    (hparentReference :
      M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2) =
        ((cwRecursiveSemanticParentTerm term hmultiplicity).split
          (sigma logicalLeg)).probability) :
    ((cwRecursiveInputProfileHoles
        partAt sigma term hmultiplicity epsilon targets reference
          (sigma logicalLeg)).card : ℝ) ≤
      ((((WordType.profileMass sourceProfile * k + 1) ^
          Fintype.card (State × (SplitWord depth × SplitWord depth)) : ℕ) : ℝ)) *
        WordType.structuralZeroMultinomialLoss sourceProfile k *
          Real.exp (((k : ℝ) * WordType.profileMass sourceProfile) *
            (M.reference.conditionalEntropy M.coarse - epsilon ^ 2 / 4)) := by
  calc
    ((cwRecursiveInputProfileHoles
        partAt sigma term hmultiplicity epsilon targets reference
          (sigma logicalLeg)).card : ℝ) ≤
        ((WordType.pooledMarginalDeviatingWordsForSource
          M.toSparsePooledMarginalProjectionModel
          (fun sample ↦ concatSplitWords sample.2.1 sample.2.2)
          state epsilon).card : ℝ) := by
      exact_mod_cast
        card_cwRecursiveInputProfileHoles_le_pooledMarginalDeviatingWords
          partAt sigma term hmultiplicity epsilon alpha targets hsupported
            hcoarseSupported reference hreference logicalLeg M state hsourceCells
              hstateReference htargetReference hparentReference
    _ ≤ _ := by
      apply WordType.card_pooledMarginalDeviatingWordsForSource_le
        M.toSparsePooledMarginalProjectionModel
        M.toSparsePooledMarginalProjectionModel_coarse
        (fun sample ↦ concatSplitWords sample.2.1 sample.2.2)
        sourceProfile hmass k hk state hsource hepsilon

end AlgebraicComplexity.Examples
