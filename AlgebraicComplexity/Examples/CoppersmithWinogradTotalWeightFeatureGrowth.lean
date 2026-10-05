/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalFeatureTypeCountingGrowth
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightFeatureCompetitorCounting

set_option autoImplicit false


/-!
# Asymptotic visible-feature bounds for total-weight CW competitors

The finite total-weight cleanup injects every directed competitor into a class that fixes only
the evaluator-visible `(pivot symbol, compatibility cell)` profile.  This file specializes the
generic conditional-feature maximum-entropy bound to those exact `Y` and `Z` alphabets.

The complete tagged atom remains the hidden target alphabet.  Consequently no injectivity of the
visible feature map is assumed: the polynomial union over hidden full types is absorbed into
`conditionalFeatureEntropyLoss`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-! ## Length reindexing -/

/-- Casting the position length of a visible-feature class preserves its cardinality.  This is
the small adapter between the library's `PositiveWord` convention (`Fin (n + 1)`) and a
proportional type count (`Fin (profileMass profile * k)`). -/
theorem card_conditionalFeatureTypeClass_cast
    {S T C : Type*} [Fintype S] [Fintype T] [Fintype C]
    {n m : ℕ} (h : n = m) (source : Fin m → S)
    (feature : T → C) (profile : S × C → ℕ) :
    (WordType.conditionalFeatureTypeClass
        (source ∘ Fin.cast h) feature profile).card =
      (WordType.conditionalFeatureTypeClass source feature profile).card := by
  subst m
  rfl

/-! ## Visible-profile source marginals -/

/-- Pushing a profile on a product alphabet through the first projection sums exactly over the
second alphabet.  This elementary identity gives generated certificates a pointwise, finite-sum
interface for the source-marginal obligation. -/
theorem mappedType_prod_fst_apply
    {S C : Type*} [Fintype S] [Fintype C]
    (profile : S × C → ℕ) (symbol : S) :
    WordType.mappedType Prod.fst profile symbol =
      ∑ cell : C, profile (symbol, cell) := by
  classical
  unfold WordType.mappedType
  apply Finset.sum_bij (fun pair _hpair ↦ pair.2)
  · intro pair _hpair
    simp
  · intro left hleft right hright hsecond
    apply Prod.ext
    · exact (WordType.mem_letterFiber.mp hleft).trans
        (WordType.mem_letterFiber.mp hright).symm
    · exact hsecond
  · intro cell _hcell
    exact ⟨(symbol, cell), WordType.mem_letterFiber.mpr rfl, rfl⟩
  · intro pair _hpair
    exact congrArg profile (Prod.ext (WordType.mem_letterFiber.mp _hpair) rfl)

/-- A uniform real bound on a finite natural-valued family also bounds the cast of its supremum.
The nonnegativity premise handles the empty family. -/
theorem cast_finset_sup_le
    {A : Type*} [DecidableEq A] (items : Finset A) (value : A → ℕ)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hvalue : ∀ item ∈ items, (value item : ℝ) ≤ bound) :
    ((items.sup value : ℕ) : ℝ) ≤ bound := by
  induction items using Finset.induction_on with
  | empty => simpa using hbound
  | @insert item items hnotmem ih =>
      rw [Finset.sup_insert]
      push_cast
      exact max_le
        (hvalue item (Finset.mem_insert_self item items))
        (ih (fun other hother ↦
          hvalue other (Finset.mem_insert_of_mem hother)))

/-- Pointwise evaluator `Y` cell sums discharge the abstract source-marginal equality used by
conditional-feature counting. -/
theorem mappedType_fst_cwTotalWeightYEvaluatorJointType_eq_of_cell_sum
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part depth)
    (sourceProfile : CWCoarseDigit depth → ℕ)
    (hcellSum : ∀ symbol,
      (∑ cell : CWTotalWeightYCell depth Part,
        (cwTotalWeightPushforwardTargets rawTargets).yCellProfile cell.1 symbol) =
      sourceProfile symbol) :
    WordType.mappedType Prod.fst
        (cwTotalWeightYEvaluatorJointType depth rawTargets) =
      sourceProfile := by
  funext symbol
  rw [mappedType_prod_fst_apply]
  simpa only [cwTotalWeightYEvaluatorJointType] using hcellSum symbol

/-- Pointwise evaluator `Z` cell sums discharge its source-marginal equality. -/
theorem mappedType_fst_cwTotalWeightZEvaluatorJointType_eq_of_cell_sum
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part depth)
    (sourceProfile : CWCoarseDigit depth → ℕ)
    (hcellSum : ∀ symbol,
      (∑ cell : CWTotalWeightZCell depth Part,
        (cwTotalWeightPushforwardTargets rawTargets).zCellProfile cell.1 symbol) =
      sourceProfile symbol) :
    WordType.mappedType Prod.fst
        (cwTotalWeightZEvaluatorJointType depth rawTargets) =
      sourceProfile := by
  funext symbol
  rw [mappedType_prod_fst_apply]
  simpa only [cwTotalWeightZEvaluatorJointType] using hcellSum symbol

/-! ## Actual positive-word classes -/

/-- The sequence-ready `Y` bound, reindexed back to the `Fin (n + 1)` convention used by
`cwTotalWeightYCompetitorFeatureClass`.

The length equality is deliberately explicit.  It is the only bridge needed between a concrete
positive-power block and the proportional source profile used by the entropy estimate. -/
theorem card_cwTotalWeightYCompetitorFeatureClass_le_loss_mul_penaltyBase_pow_of_length
    (depth n : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (sourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (rawTargets : CompatibilityTargets Part depth)
    (label : PositiveWord (CWCoarseDigit depth) n)
    (jointExponentPerRepetition : ℝ)
    (hlength : n + 1 = WordType.profileMass sourceProfile * k)
    (hmass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : WordType.multiplicity
        (positiveWordEquiv (CWCoarseDigit depth) n label) =
      WordType.proportionalCounts sourceProfile k)
    (hfeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightYEvaluatorJointType depth rawTargets) =
        WordType.multiplicity
          (positiveWordEquiv (CWCoarseDigit depth) n label))
    (hexponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)
        (WordType.profileMass sourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    ((cwTotalWeightYCompetitorFeatureClass
        depth n rawTargets label).card : ℝ) ≤
      WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
  classical
  let original : Fin (n + 1) → CWCoarseDigit depth :=
    positiveWordEquiv (CWCoarseDigit depth) n label
  let source : Fin (WordType.profileMass sourceProfile * k) → CWCoarseDigit depth :=
    original ∘ Fin.cast hlength.symm
  have hsourceCast : WordType.multiplicity source =
      WordType.proportionalCounts sourceProfile k := by
    change WordType.multiplicity (original ∘ Fin.cast hlength.symm) = _
    exact (WordType.multiplicity_cast hlength.symm original).trans hsource
  have hfeatureSourceCast :
      WordType.mappedType Prod.fst
          (cwTotalWeightYEvaluatorJointType depth rawTargets) =
        WordType.multiplicity source := by
    change WordType.mappedType Prod.fst
        (cwTotalWeightYEvaluatorJointType depth rawTargets) =
      WordType.multiplicity (original ∘ Fin.cast hlength.symm)
    exact hfeatureSource.trans
      (WordType.multiplicity_cast hlength.symm original).symm
  have hbound := WordType.card_conditionalFeatureTypeClass_le_entropyLoss_mul_penaltyBase_pow
    (CWTotalWeightTaggedAtom depth Part) sourceProfile k source
      (cwTotalWeightYFiniteCellOfTaggedAtom depth)
      (cwTotalWeightYEvaluatorJointType depth rawTargets)
      jointExponentPerRepetition hmass hk hsourceCast
      (fun jointType hjointType ↦
        WordType.mappedType_fst_eq_of_mem_feasibleConditionalFeatureTypes
          (cwTotalWeightYFiniteCellOfTaggedAtom depth)
          (cwTotalWeightYEvaluatorJointType depth rawTargets)
          (WordType.profileMass sourceProfile * k)
          (WordType.multiplicity source) hfeatureSourceCast hjointType)
      hexponent
  have hcard := card_conditionalFeatureTypeClass_cast hlength.symm original
    (cwTotalWeightYFiniteCellOfTaggedAtom depth)
    (cwTotalWeightYEvaluatorJointType depth rawTargets)
  simpa only [cwTotalWeightYCompetitorFeatureClass, source, original, hcard] using hbound

/-- The analogous reindexed bound for an actual total-weight `Z` competitor class. -/
theorem card_cwTotalWeightZCompetitorFeatureClass_le_loss_mul_penaltyBase_pow_of_length
    (depth n : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (sourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (rawTargets : CompatibilityTargets Part depth)
    (label : PositiveWord (CWCoarseDigit depth) n)
    (jointExponentPerRepetition : ℝ)
    (hlength : n + 1 = WordType.profileMass sourceProfile * k)
    (hmass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : WordType.multiplicity
        (positiveWordEquiv (CWCoarseDigit depth) n label) =
      WordType.proportionalCounts sourceProfile k)
    (hfeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightZEvaluatorJointType depth rawTargets) =
        WordType.multiplicity
          (positiveWordEquiv (CWCoarseDigit depth) n label))
    (hexponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)
        (WordType.profileMass sourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    ((cwTotalWeightZCompetitorFeatureClass
        depth n rawTargets label).card : ℝ) ≤
      WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
  classical
  let original : Fin (n + 1) → CWCoarseDigit depth :=
    positiveWordEquiv (CWCoarseDigit depth) n label
  let source : Fin (WordType.profileMass sourceProfile * k) → CWCoarseDigit depth :=
    original ∘ Fin.cast hlength.symm
  have hsourceCast : WordType.multiplicity source =
      WordType.proportionalCounts sourceProfile k := by
    change WordType.multiplicity (original ∘ Fin.cast hlength.symm) = _
    exact (WordType.multiplicity_cast hlength.symm original).trans hsource
  have hfeatureSourceCast :
      WordType.mappedType Prod.fst
          (cwTotalWeightZEvaluatorJointType depth rawTargets) =
        WordType.multiplicity source := by
    change WordType.mappedType Prod.fst
        (cwTotalWeightZEvaluatorJointType depth rawTargets) =
      WordType.multiplicity (original ∘ Fin.cast hlength.symm)
    exact hfeatureSource.trans
      (WordType.multiplicity_cast hlength.symm original).symm
  have hbound := WordType.card_conditionalFeatureTypeClass_le_entropyLoss_mul_penaltyBase_pow
    (CWTotalWeightTaggedAtom depth Part) sourceProfile k source
      (cwTotalWeightZFiniteCellOfTaggedAtom depth)
      (cwTotalWeightZEvaluatorJointType depth rawTargets)
      jointExponentPerRepetition hmass hk hsourceCast
      (fun jointType hjointType ↦
        WordType.mappedType_fst_eq_of_mem_feasibleConditionalFeatureTypes
          (cwTotalWeightZFiniteCellOfTaggedAtom depth)
          (cwTotalWeightZEvaluatorJointType depth rawTargets)
          (WordType.profileMass sourceProfile * k)
          (WordType.multiplicity source) hfeatureSourceCast hjointType)
      hexponent
  have hcard := card_conditionalFeatureTypeClass_cast hlength.symm original
    (cwTotalWeightZFiniteCellOfTaggedAtom depth)
    (cwTotalWeightZEvaluatorJointType depth rawTargets)
  simpa only [cwTotalWeightZCompetitorFeatureClass, source, original, hcard] using hbound

/-! ## One visible class -/

/-- Sequence-ready maximum-entropy bound for one total-weight `Y` competitor class.

`jointExponentPerRepetition` is the certificate's uniform upper bound on
`mass(jointType) * H(jointType)` for every hidden full tagged-atom type that has the prescribed
visible `(Y symbol, Y cell)` profile. -/
theorem card_cwTotalWeightYVisibleClass_le_loss_mul_penaltyBase_pow
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (sourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (source : Fin (WordType.profileMass sourceProfile * k) → CWCoarseDigit depth)
    (rawTargets : CompatibilityTargets Part depth)
    (jointExponentPerRepetition : ℝ)
    (hmass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : WordType.multiplicity source =
      WordType.proportionalCounts sourceProfile k)
    (hfeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightYEvaluatorJointType depth rawTargets) =
        WordType.multiplicity source)
    (hexponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)
        (WordType.profileMass sourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    ((WordType.conditionalFeatureTypeClass source
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)).card : ℝ) ≤
      WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
  classical
  apply WordType.card_conditionalFeatureTypeClass_le_entropyLoss_mul_penaltyBase_pow
    (CWTotalWeightTaggedAtom depth Part) sourceProfile k source
      (cwTotalWeightYFiniteCellOfTaggedAtom depth)
      (cwTotalWeightYEvaluatorJointType depth rawTargets)
      jointExponentPerRepetition hmass hk hsource
  · intro jointType hjointType
    exact WordType.mappedType_fst_eq_of_mem_feasibleConditionalFeatureTypes
      (cwTotalWeightYFiniteCellOfTaggedAtom depth)
      (cwTotalWeightYEvaluatorJointType depth rawTargets)
      (WordType.profileMass sourceProfile * k)
      (WordType.multiplicity source) hfeatureSource hjointType
  · exact hexponent

/-- Sequence-ready maximum-entropy bound for one total-weight `Z` competitor class. -/
theorem card_cwTotalWeightZVisibleClass_le_loss_mul_penaltyBase_pow
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (sourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (source : Fin (WordType.profileMass sourceProfile * k) → CWCoarseDigit depth)
    (rawTargets : CompatibilityTargets Part depth)
    (jointExponentPerRepetition : ℝ)
    (hmass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : WordType.multiplicity source =
      WordType.proportionalCounts sourceProfile k)
    (hfeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightZEvaluatorJointType depth rawTargets) =
        WordType.multiplicity source)
    (hexponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)
        (WordType.profileMass sourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    ((WordType.conditionalFeatureTypeClass source
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)).card : ℝ) ≤
      WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
  classical
  apply WordType.card_conditionalFeatureTypeClass_le_entropyLoss_mul_penaltyBase_pow
    (CWTotalWeightTaggedAtom depth Part) sourceProfile k source
      (cwTotalWeightZFiniteCellOfTaggedAtom depth)
      (cwTotalWeightZEvaluatorJointType depth rawTargets)
      jointExponentPerRepetition hmass hk hsource
  · intro jointType hjointType
    exact WordType.mappedType_fst_eq_of_mem_feasibleConditionalFeatureTypes
      (cwTotalWeightZFiniteCellOfTaggedAtom depth)
      (cwTotalWeightZEvaluatorJointType depth rawTargets)
      (WordType.profileMass sourceProfile * k)
      (WordType.multiplicity source) hfeatureSource hjointType
  · exact hexponent

/-! ## Uniform finite families of pivot words -/

/-- Summed `Y` bound for any finite family of pivot words with the same prescribed source type.
This is the exact algebra needed after the source-aware competitor injection: the ambient-family
factor is explicit, while all hidden-type overhead remains subexponential. -/
theorem sum_card_cwTotalWeightYVisibleClass_le_card_mul_loss_mul_penaltyBase_pow
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (sourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (sources : Finset
      (Fin (WordType.profileMass sourceProfile * k) → CWCoarseDigit depth))
    (rawTargets : CompatibilityTargets Part depth)
    (jointExponentPerRepetition : ℝ)
    (hmass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : ∀ source ∈ sources,
      WordType.multiplicity source = WordType.proportionalCounts sourceProfile k)
    (hfeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightYEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts sourceProfile k)
    (hexponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)
        (WordType.profileMass sourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    (∑ source ∈ sources,
      ((WordType.conditionalFeatureTypeClass source
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)).card : ℝ)) ≤
      (sources.card : ℝ) *
        WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
  classical
  calc
    (∑ source ∈ sources,
      ((WordType.conditionalFeatureTypeClass source
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)).card : ℝ)) ≤
        ∑ _source ∈ sources,
          WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
            WordType.conditionalFeatureEntropyPenaltyBase
              sourceProfile jointExponentPerRepetition ^ k := by
      apply Finset.sum_le_sum
      intro source hsourceMem
      exact card_cwTotalWeightYVisibleClass_le_loss_mul_penaltyBase_pow
        depth sourceProfile k source rawTargets jointExponentPerRepetition
        hmass hk (hsource source hsourceMem)
        (hfeatureSource.trans (hsource source hsourceMem).symm) hexponent
    _ = (sources.card : ℝ) *
        WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Summed `Z` bound for any finite family of pivot words with one prescribed source type. -/
theorem sum_card_cwTotalWeightZVisibleClass_le_card_mul_loss_mul_penaltyBase_pow
    (depth : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (sourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (sources : Finset
      (Fin (WordType.profileMass sourceProfile * k) → CWCoarseDigit depth))
    (rawTargets : CompatibilityTargets Part depth)
    (jointExponentPerRepetition : ℝ)
    (hmass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : ∀ source ∈ sources,
      WordType.multiplicity source = WordType.proportionalCounts sourceProfile k)
    (hfeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightZEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts sourceProfile k)
    (hexponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)
        (WordType.profileMass sourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    (∑ source ∈ sources,
      ((WordType.conditionalFeatureTypeClass source
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)).card : ℝ)) ≤
      (sources.card : ℝ) *
        WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
  classical
  calc
    (∑ source ∈ sources,
      ((WordType.conditionalFeatureTypeClass source
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)).card : ℝ)) ≤
        ∑ _source ∈ sources,
          WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
            WordType.conditionalFeatureEntropyPenaltyBase
              sourceProfile jointExponentPerRepetition ^ k := by
      apply Finset.sum_le_sum
      intro source hsourceMem
      exact card_cwTotalWeightZVisibleClass_le_loss_mul_penaltyBase_pow
        depth sourceProfile k source rawTargets jointExponentPerRepetition
        hmass hk (hsource source hsourceMem)
        (hfeatureSource.trans (hsource source hsourceMem).symm) hexponent
    _ = (sources.card : ℝ) *
        WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-! ## Actual finite address families -/

/-- Visible `Y`-competitor classes summed over an actual finite family of CW block addresses.
Unlike an image finset of pivot labels, this keeps repeated labels with their source addresses,
which is exactly what the directed-incidence cleanup count requires. -/
theorem sum_address_card_cwTotalWeightYCompetitorFeatureClass_le
    (depth n : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (sourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (jointExponentPerRepetition : ℝ)
    (hlength : n + 1 = WordType.profileMass sourceProfile * k)
    (hmass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : ∀ address ∈ ambient,
      WordType.multiplicity
          (positiveWordEquiv (CWCoarseDigit depth) n (address .Y)) =
        WordType.proportionalCounts sourceProfile k)
    (hfeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightYEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts sourceProfile k)
    (hexponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)
        (WordType.profileMass sourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    (∑ address ∈ ambient,
      ((cwTotalWeightYCompetitorFeatureClass
        depth n rawTargets (address .Y)).card : ℝ)) ≤
      (ambient.card : ℝ) *
        WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
  classical
  calc
    (∑ address ∈ ambient,
      ((cwTotalWeightYCompetitorFeatureClass
        depth n rawTargets (address .Y)).card : ℝ)) ≤
        ∑ _address ∈ ambient,
          WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
            WordType.conditionalFeatureEntropyPenaltyBase
              sourceProfile jointExponentPerRepetition ^ k := by
      apply Finset.sum_le_sum
      intro address haddress
      exact
        card_cwTotalWeightYCompetitorFeatureClass_le_loss_mul_penaltyBase_pow_of_length
          depth n sourceProfile k rawTargets (address .Y)
          jointExponentPerRepetition hlength hmass hk (hsource address haddress)
          (hfeatureSource.trans (hsource address haddress).symm) hexponent
    _ = (ambient.card : ℝ) *
        WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Visible `Z`-competitor classes summed over an actual finite address family. -/
theorem sum_address_card_cwTotalWeightZCompetitorFeatureClass_le
    (depth n : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (sourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (jointExponentPerRepetition : ℝ)
    (hlength : n + 1 = WordType.profileMass sourceProfile * k)
    (hmass : 0 < WordType.profileMass sourceProfile) (hk : 0 < k)
    (hsource : ∀ address ∈ ambient,
      WordType.multiplicity
          (positiveWordEquiv (CWCoarseDigit depth) n (address .Z)) =
        WordType.proportionalCounts sourceProfile k)
    (hfeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightZEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts sourceProfile k)
    (hexponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)
        (WordType.profileMass sourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * jointExponentPerRepetition) :
    (∑ address ∈ ambient,
      ((cwTotalWeightZCompetitorFeatureClass
        depth n rawTargets (address .Z)).card : ℝ)) ≤
      (ambient.card : ℝ) *
        WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
  classical
  calc
    (∑ address ∈ ambient,
      ((cwTotalWeightZCompetitorFeatureClass
        depth n rawTargets (address .Z)).card : ℝ)) ≤
        ∑ _address ∈ ambient,
          WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
            WordType.conditionalFeatureEntropyPenaltyBase
              sourceProfile jointExponentPerRepetition ^ k := by
      apply Finset.sum_le_sum
      intro address haddress
      exact
        card_cwTotalWeightZCompetitorFeatureClass_le_loss_mul_penaltyBase_pow_of_length
          depth n sourceProfile k rawTargets (address .Z)
          jointExponentPerRepetition hlength hmass hk (hsource address haddress)
          (hfeatureSource.trans (hsource address haddress).symm) hexponent
    _ = (ambient.card : ℝ) *
        WordType.conditionalFeatureEntropyLoss
          (CWTotalWeightTaggedAtom depth Part) sourceProfile k *
        WordType.conditionalFeatureEntropyPenaltyBase
          sourceProfile jointExponentPerRepetition ^ k := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-! ## Sequence-ready compatibility part of the outer field requirement -/

/-- Exact natural compatibility half-retention requirement obtained from the largest
evaluator-visible `Y` and `Z` competitor classes in the actual target family.

This is not the initial `X`-isolation requirement.  A sound outer hash field must dominate the
maximum of this value and `4 * |xCompetitorYIndices|`. -/
noncomputable def cwTotalWeightVisibleCompetitorRequirement
    (depth n : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part depth)
    (targets : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) : ℕ :=
  4 *
    ((targets.sup fun target ↦
        (cwTotalWeightYCompetitorFeatureClass
          depth n rawTargets (target .Y)).card) +
      (targets.sup fun target ↦
        (cwTotalWeightZCompetitorFeatureClass
          depth n rawTargets (target .Z)).card))

/-- Every actual target satisfies the exact natural `Y/Z` compatibility budget. -/
theorem four_mul_add_cwTotalWeightVisibleClass_cards_le_requirement
    (depth n : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part depth)
    (targets : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (target : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (htarget : target ∈ targets) :
    4 *
        ((cwTotalWeightYCompetitorFeatureClass
            depth n rawTargets (target .Y)).card +
          (cwTotalWeightZCompetitorFeatureClass
            depth n rawTargets (target .Z)).card) ≤
    cwTotalWeightVisibleCompetitorRequirement
        depth n rawTargets targets := by
  let fy : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) → ℕ :=
    fun address ↦
      (cwTotalWeightYCompetitorFeatureClass
        depth n rawTargets (address .Y)).card
  let fz : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) → ℕ :=
    fun address ↦
      (cwTotalWeightZCompetitorFeatureClass
        depth n rawTargets (address .Z)).card
  have hY : fy target ≤ targets.sup fy := Finset.le_sup htarget
  have hZ : fz target ≤ targets.sup fz := Finset.le_sup htarget
  unfold cwTotalWeightVisibleCompetitorRequirement
  apply Nat.mul_le_mul_left 4
  simpa only [fy, fz] using Nat.add_le_add hY hZ

/-- The subexponential factor in a field requirement that simultaneously dominates one `Y`
and one `Z` visible competitor class.  The factor four is the constant that turns their sum into
the half-retention incidence budget; the separate affine `X` quarter budget is not included. -/
noncomputable def cwTotalWeightVisibleFeatureFieldLoss
    (depth : ℕ) (Part : Type) [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ)
    (k : ℕ) : ℝ :=
  4 *
    (WordType.conditionalFeatureEntropyLoss
        (CWTotalWeightTaggedAtom depth Part) ySourceProfile k +
      WordType.conditionalFeatureEntropyLoss
        (CWTotalWeightTaggedAtom depth Part) zSourceProfile k)

theorem cwTotalWeightVisibleFeatureFieldLoss_pos
    (depth : ℕ) (Part : Type) [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ)
    (k : ℕ) :
    0 < cwTotalWeightVisibleFeatureFieldLoss
      depth Part ySourceProfile zSourceProfile k := by
  unfold cwTotalWeightVisibleFeatureFieldLoss
  exact mul_pos (by norm_num) (add_pos
    (WordType.conditionalFeatureEntropyLoss_pos
      (CWTotalWeightTaggedAtom depth Part) ySourceProfile k)
    (WordType.conditionalFeatureEntropyLoss_pos
      (CWTotalWeightTaggedAtom depth Part) zSourceProfile k))

/-- All polynomial hidden-type selection factors in the outer field requirement are
subexponential. -/
theorem cwTotalWeightVisibleFeatureFieldLoss_subexponential
    (depth : ℕ) (Part : Type) [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ) :
    Growth.Subexponential
      (cwTotalWeightVisibleFeatureFieldLoss
        depth Part ySourceProfile zSourceProfile) := by
  have hy := WordType.conditionalFeatureEntropyLoss_subexponential
    (CWTotalWeightTaggedAtom depth Part) ySourceProfile
  have hz := WordType.conditionalFeatureEntropyLoss_subexponential
    (CWTotalWeightTaggedAtom depth Part) zSourceProfile
  change Growth.Subexponential (fun n ↦
    4 * (WordType.conditionalFeatureEntropyLoss
      (CWTotalWeightTaggedAtom depth Part) ySourceProfile n +
      WordType.conditionalFeatureEntropyLoss
        (CWTotalWeightTaggedAtom depth Part) zSourceProfile n))
  exact (hy.add hz).const_mul (show (0 : ℝ) ≤ 4 by norm_num)

/-- One exponential base dominating both directed visible-class penalty bases and `1`.
The extra maximum with `1` is rate-neutral whenever a competitor class grows exponentially, and
is exactly the normalization required by the canonical prime-field sizing theorem. -/
noncomputable def cwTotalWeightVisibleFeatureFieldBase
    {depth : ℕ}
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ) : ℝ :=
  max 1 (max
    (WordType.conditionalFeatureEntropyPenaltyBase
      ySourceProfile yJointExponentPerRepetition)
    (WordType.conditionalFeatureEntropyPenaltyBase
      zSourceProfile zJointExponentPerRepetition))

theorem cwTotalWeightVisibleFeatureFieldBase_pos
    {depth : ℕ}
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ) :
    0 < cwTotalWeightVisibleFeatureFieldBase
      ySourceProfile zSourceProfile
      yJointExponentPerRepetition zJointExponentPerRepetition := by
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem one_le_cwTotalWeightVisibleFeatureFieldBase
    {depth : ℕ}
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ) :
    1 ≤ cwTotalWeightVisibleFeatureFieldBase
      ySourceProfile zSourceProfile
      yJointExponentPerRepetition zJointExponentPerRepetition :=
  le_max_left _ _

/-- Exact real compatibility-budget bound for one pair of actual total-weight pivot labels.

This is the `Y/Z` part of the numerical-growth boundary needed by a canonical prime-field
constructor.  Prime sizing may add another fixed factor, but the compatibility contribution has
the maximum of the two certificate-visible conditional-entropy bases.  The final outer base must
also include the independent `X`-fiber base. -/
theorem four_mul_add_cwTotalWeightVisibleClasses_le_fieldLoss_mul_fieldBase_pow
    (depth n : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (rawTargets : CompatibilityTargets Part depth)
    (yLabel zLabel : PositiveWord (CWCoarseDigit depth) n)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hyLength : n + 1 = WordType.profileMass ySourceProfile * k)
    (hzLength : n + 1 = WordType.profileMass zSourceProfile * k)
    (hyMass : 0 < WordType.profileMass ySourceProfile)
    (hzMass : 0 < WordType.profileMass zSourceProfile) (hk : 0 < k)
    (hySource : WordType.multiplicity
        (positiveWordEquiv (CWCoarseDigit depth) n yLabel) =
      WordType.proportionalCounts ySourceProfile k)
    (hzSource : WordType.multiplicity
        (positiveWordEquiv (CWCoarseDigit depth) n zLabel) =
      WordType.proportionalCounts zSourceProfile k)
    (hyFeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightYEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts ySourceProfile k)
    (hzFeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightZEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts zSourceProfile k)
    (hyExponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)
        (WordType.profileMass ySourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * yJointExponentPerRepetition)
    (hzExponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)
        (WordType.profileMass zSourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * zJointExponentPerRepetition) :
    4 *
        (((cwTotalWeightYCompetitorFeatureClass
            depth n rawTargets yLabel).card : ℝ) +
          ((cwTotalWeightZCompetitorFeatureClass
            depth n rawTargets zLabel).card : ℝ)) ≤
      cwTotalWeightVisibleFeatureFieldLoss
          depth Part ySourceProfile zSourceProfile k *
        cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition ^ k := by
  have hy :=
    card_cwTotalWeightYCompetitorFeatureClass_le_loss_mul_penaltyBase_pow_of_length
      depth n ySourceProfile k rawTargets yLabel yJointExponentPerRepetition
      hyLength hyMass hk hySource
      (hyFeatureSource.trans hySource.symm) hyExponent
  have hz :=
    card_cwTotalWeightZCompetitorFeatureClass_le_loss_mul_penaltyBase_pow_of_length
      depth n zSourceProfile k rawTargets zLabel zJointExponentPerRepetition
      hzLength hzMass hk hzSource
      (hzFeatureSource.trans hzSource.symm) hzExponent
  have hyBase :
      WordType.conditionalFeatureEntropyPenaltyBase
          ySourceProfile yJointExponentPerRepetition ^ k ≤
        cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition ^ k := by
    exact pow_le_pow_left₀
      (le_of_lt (WordType.conditionalFeatureEntropyPenaltyBase_pos
        ySourceProfile yJointExponentPerRepetition))
      ((le_max_left _ _).trans (le_max_right _ _)) k
  have hzBase :
      WordType.conditionalFeatureEntropyPenaltyBase
          zSourceProfile zJointExponentPerRepetition ^ k ≤
        cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition ^ k := by
    exact pow_le_pow_left₀
      (le_of_lt (WordType.conditionalFeatureEntropyPenaltyBase_pos
        zSourceProfile zJointExponentPerRepetition))
      ((le_max_right _ _).trans (le_max_right _ _)) k
  calc
    4 *
        (((cwTotalWeightYCompetitorFeatureClass
            depth n rawTargets yLabel).card : ℝ) +
          ((cwTotalWeightZCompetitorFeatureClass
            depth n rawTargets zLabel).card : ℝ)) ≤
        4 *
          (WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) ySourceProfile k *
              WordType.conditionalFeatureEntropyPenaltyBase
                ySourceProfile yJointExponentPerRepetition ^ k +
            WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) zSourceProfile k *
              WordType.conditionalFeatureEntropyPenaltyBase
                zSourceProfile zJointExponentPerRepetition ^ k) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hy hz) (by norm_num)
    _ ≤ 4 *
          (WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) ySourceProfile k *
              cwTotalWeightVisibleFeatureFieldBase
                ySourceProfile zSourceProfile
                yJointExponentPerRepetition zJointExponentPerRepetition ^ k +
            WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) zSourceProfile k *
              cwTotalWeightVisibleFeatureFieldBase
                ySourceProfile zSourceProfile
                yJointExponentPerRepetition zJointExponentPerRepetition ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hyBase
          (le_of_lt (WordType.conditionalFeatureEntropyLoss_pos
            (CWTotalWeightTaggedAtom depth Part) ySourceProfile k)))
        (mul_le_mul_of_nonneg_left hzBase
          (le_of_lt (WordType.conditionalFeatureEntropyLoss_pos
            (CWTotalWeightTaggedAtom depth Part) zSourceProfile k)))
    _ = cwTotalWeightVisibleFeatureFieldLoss
          depth Part ySourceProfile zSourceProfile k *
        cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition ^ k := by
      unfold cwTotalWeightVisibleFeatureFieldLoss
      ring

/-- The exact target-family supremum requirement has the same sequence-ready field bound.

This closes the compatibility half of the quantitative premise consumed by
`CWTotalWeightLocalizedOuterSequenceData.ofCombinedPrimeFullBucketCount`: no maximum over all
words is taken, only the actual pre-seed target family.  The constructor separately requires the
initial `X`-fiber bound. -/
theorem cwTotalWeightVisibleCompetitorRequirement_cast_le_fieldLoss_mul_fieldBase_pow
    (depth n : ℕ) {Part : Type} [Fintype Part] [DecidableEq Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (rawTargets : CompatibilityTargets Part depth)
    (targets : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hyLength : n + 1 = WordType.profileMass ySourceProfile * k)
    (hzLength : n + 1 = WordType.profileMass zSourceProfile * k)
    (hyMass : 0 < WordType.profileMass ySourceProfile)
    (hzMass : 0 < WordType.profileMass zSourceProfile) (hk : 0 < k)
    (hySource : ∀ target ∈ targets,
      WordType.multiplicity
          (positiveWordEquiv (CWCoarseDigit depth) n (target .Y)) =
        WordType.proportionalCounts ySourceProfile k)
    (hzSource : ∀ target ∈ targets,
      WordType.multiplicity
          (positiveWordEquiv (CWCoarseDigit depth) n (target .Z)) =
        WordType.proportionalCounts zSourceProfile k)
    (hyFeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightYEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts ySourceProfile k)
    (hzFeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightZEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts zSourceProfile k)
    (hyExponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)
        (WordType.profileMass ySourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * yJointExponentPerRepetition)
    (hzExponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)
        (WordType.profileMass zSourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * zJointExponentPerRepetition) :
    (cwTotalWeightVisibleCompetitorRequirement
        depth n rawTargets targets : ℝ) ≤
      cwTotalWeightVisibleFeatureFieldLoss
          depth Part ySourceProfile zSourceProfile k *
        cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition ^ k := by
  let yBound : ℝ :=
    WordType.conditionalFeatureEntropyLoss
        (CWTotalWeightTaggedAtom depth Part) ySourceProfile k *
      WordType.conditionalFeatureEntropyPenaltyBase
        ySourceProfile yJointExponentPerRepetition ^ k
  let zBound : ℝ :=
    WordType.conditionalFeatureEntropyLoss
        (CWTotalWeightTaggedAtom depth Part) zSourceProfile k *
      WordType.conditionalFeatureEntropyPenaltyBase
        zSourceProfile zJointExponentPerRepetition ^ k
  have hyEach : ∀ target ∈ targets,
      ((cwTotalWeightYCompetitorFeatureClass
        depth n rawTargets (target .Y)).card : ℝ) ≤ yBound := by
    intro target htarget
    exact card_cwTotalWeightYCompetitorFeatureClass_le_loss_mul_penaltyBase_pow_of_length
      depth n ySourceProfile k rawTargets (target .Y)
      yJointExponentPerRepetition hyLength hyMass hk (hySource target htarget)
      (hyFeatureSource.trans (hySource target htarget).symm) hyExponent
  have hzEach : ∀ target ∈ targets,
      ((cwTotalWeightZCompetitorFeatureClass
        depth n rawTargets (target .Z)).card : ℝ) ≤ zBound := by
    intro target htarget
    exact card_cwTotalWeightZCompetitorFeatureClass_le_loss_mul_penaltyBase_pow_of_length
      depth n zSourceProfile k rawTargets (target .Z)
      zJointExponentPerRepetition hzLength hzMass hk (hzSource target htarget)
      (hzFeatureSource.trans (hzSource target htarget).symm) hzExponent
  have hyBoundNonneg : 0 ≤ yBound := by
    dsimp only [yBound]
    exact mul_nonneg
      (le_of_lt (WordType.conditionalFeatureEntropyLoss_pos
        (CWTotalWeightTaggedAtom depth Part) ySourceProfile k))
      (pow_nonneg (le_of_lt
        (WordType.conditionalFeatureEntropyPenaltyBase_pos
          ySourceProfile yJointExponentPerRepetition)) k)
  have hzBoundNonneg : 0 ≤ zBound := by
    dsimp only [zBound]
    exact mul_nonneg
      (le_of_lt (WordType.conditionalFeatureEntropyLoss_pos
        (CWTotalWeightTaggedAtom depth Part) zSourceProfile k))
      (pow_nonneg (le_of_lt
        (WordType.conditionalFeatureEntropyPenaltyBase_pos
          zSourceProfile zJointExponentPerRepetition)) k)
  have hyMaximum :
      ((targets.sup (fun target ↦
        (cwTotalWeightYCompetitorFeatureClass
          depth n rawTargets (target .Y)).card) : ℕ) : ℝ) ≤ yBound :=
    cast_finset_sup_le targets _ yBound hyBoundNonneg hyEach
  have hzMaximum :
      ((targets.sup (fun target ↦
        (cwTotalWeightZCompetitorFeatureClass
          depth n rawTargets (target .Z)).card) : ℕ) : ℝ) ≤ zBound :=
    cast_finset_sup_le targets _ zBound hzBoundNonneg hzEach
  have hyBase :
      WordType.conditionalFeatureEntropyPenaltyBase
          ySourceProfile yJointExponentPerRepetition ^ k ≤
        cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition ^ k := by
    exact pow_le_pow_left₀
      (le_of_lt (WordType.conditionalFeatureEntropyPenaltyBase_pos
        ySourceProfile yJointExponentPerRepetition))
      ((le_max_left _ _).trans (le_max_right _ _)) k
  have hzBase :
      WordType.conditionalFeatureEntropyPenaltyBase
          zSourceProfile zJointExponentPerRepetition ^ k ≤
        cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition ^ k := by
    exact pow_le_pow_left₀
      (le_of_lt (WordType.conditionalFeatureEntropyPenaltyBase_pos
        zSourceProfile zJointExponentPerRepetition))
      ((le_max_right _ _).trans (le_max_right _ _)) k
  calc
    (cwTotalWeightVisibleCompetitorRequirement
        depth n rawTargets targets : ℝ) =
        4 *
          (((targets.sup (fun target ↦
            (cwTotalWeightYCompetitorFeatureClass
              depth n rawTargets (target .Y)).card) : ℕ) : ℝ) +
          ((targets.sup (fun target ↦
            (cwTotalWeightZCompetitorFeatureClass
              depth n rawTargets (target .Z)).card) : ℕ) : ℝ)) := by
      simp only [cwTotalWeightVisibleCompetitorRequirement, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_add]
    _ ≤ 4 * (yBound + zBound) :=
      mul_le_mul_of_nonneg_left (add_le_add hyMaximum hzMaximum) (by norm_num)
    _ ≤ 4 *
          (WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) ySourceProfile k *
              cwTotalWeightVisibleFeatureFieldBase
                ySourceProfile zSourceProfile
                yJointExponentPerRepetition zJointExponentPerRepetition ^ k +
            WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) zSourceProfile k *
              cwTotalWeightVisibleFeatureFieldBase
                ySourceProfile zSourceProfile
                yJointExponentPerRepetition zJointExponentPerRepetition ^ k) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hyBase
          (le_of_lt (WordType.conditionalFeatureEntropyLoss_pos
            (CWTotalWeightTaggedAtom depth Part) ySourceProfile k)))
        (mul_le_mul_of_nonneg_left hzBase
          (le_of_lt (WordType.conditionalFeatureEntropyLoss_pos
            (CWTotalWeightTaggedAtom depth Part) zSourceProfile k)))
    _ = cwTotalWeightVisibleFeatureFieldLoss
          depth Part ySourceProfile zSourceProfile k *
        cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition ^ k := by
      unfold cwTotalWeightVisibleFeatureFieldLoss
      ring

/-! ## No-hole aggregate with visible-feature growth -/

/-- The finite total-weight no-hole count with both directed competitor sums replaced by their
sequence-ready visible-feature entropy bounds.

This theorem deliberately keeps the two pivot profiles and their two entropy exponents separate.
It therefore records exactly the outer compatibility contribution and makes no claim about where
an inner marked-fiber (`E2`) exponent is accounted for. -/
theorem cwTotalWeight_card_ambient_real_le_card_YZIsolatedSupport_add_visibleGrowth
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ) (k : ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hyLength : n + 1 = WordType.profileMass ySourceProfile * k)
    (hzLength : n + 1 = WordType.profileMass zSourceProfile * k)
    (hyMass : 0 < WordType.profileMass ySourceProfile)
    (hzMass : 0 < WordType.profileMass zSourceProfile) (hk : 0 < k)
    (hySource : ∀ address ∈ ambient,
      WordType.multiplicity
          (positiveWordEquiv (CWCoarseDigit depth) n (address .Y)) =
        WordType.proportionalCounts ySourceProfile k)
    (hzSource : ∀ address ∈
        cwTotalWeightYIsolatedSupport depth n partAt rawTargets ambient,
      WordType.multiplicity
          (positiveWordEquiv (CWCoarseDigit depth) n (address .Z)) =
        WordType.proportionalCounts zSourceProfile k)
    (hyFeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightYEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts ySourceProfile k)
    (hzFeatureSource :
      WordType.mappedType Prod.fst
          (cwTotalWeightZEvaluatorJointType depth rawTargets) =
        WordType.proportionalCounts zSourceProfile k)
    (hyExponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightYFiniteCellOfTaggedAtom depth)
        (cwTotalWeightYEvaluatorJointType depth rawTargets)
        (WordType.profileMass ySourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * yJointExponentPerRepetition)
    (hzExponent : ∀ jointType ∈
      WordType.feasibleConditionalFeatureTypes
        (cwTotalWeightZFiniteCellOfTaggedAtom depth)
        (cwTotalWeightZEvaluatorJointType depth rawTargets)
        (WordType.profileMass zSourceProfile * k),
      (WordType.profileMass jointType : ℝ) *
          WordType.profileEntropyNats jointType ≤
        (k : ℝ) * zJointExponentPerRepetition) :
    (ambient.card : ℝ) ≤
      ((cwTotalWeightYZIsolatedSupport
          depth n partAt rawTargets ambient).card : ℝ) +
        (ambient.card : ℝ) *
          WordType.conditionalFeatureEntropyLoss
            (CWTotalWeightTaggedAtom depth Part) ySourceProfile k *
          WordType.conditionalFeatureEntropyPenaltyBase
            ySourceProfile yJointExponentPerRepetition ^ k +
        ((cwTotalWeightYIsolatedSupport
            depth n partAt rawTargets ambient).card : ℝ) *
          WordType.conditionalFeatureEntropyLoss
            (CWTotalWeightTaggedAtom depth Part) zSourceProfile k *
          WordType.conditionalFeatureEntropyPenaltyBase
            zSourceProfile zJointExponentPerRepetition ^ k := by
  classical
  have hfinite :=
    cwTotalWeight_card_ambient_le_card_YZIsolatedSupport_add_featureTypeCounts
      K q depth n partAt rawTargets ambient hambient
  have hfiniteReal : (ambient.card : ℝ) ≤
      ((cwTotalWeightYZIsolatedSupport
          depth n partAt rawTargets ambient).card : ℝ) +
        (∑ address ∈ ambient,
          ((cwTotalWeightYCompetitorFeatureClass
            depth n rawTargets (address .Y)).card : ℝ)) +
        (∑ address ∈ cwTotalWeightYIsolatedSupport
            depth n partAt rawTargets ambient,
          ((cwTotalWeightZCompetitorFeatureClass
            depth n rawTargets (address .Z)).card : ℝ)) := by
    exact_mod_cast hfinite
  calc
    (ambient.card : ℝ) ≤
        ((cwTotalWeightYZIsolatedSupport
            depth n partAt rawTargets ambient).card : ℝ) +
          (∑ address ∈ ambient,
            ((cwTotalWeightYCompetitorFeatureClass
              depth n rawTargets (address .Y)).card : ℝ)) +
          (∑ address ∈ cwTotalWeightYIsolatedSupport
              depth n partAt rawTargets ambient,
            ((cwTotalWeightZCompetitorFeatureClass
              depth n rawTargets (address .Z)).card : ℝ)) := hfiniteReal
    _ ≤ ((cwTotalWeightYZIsolatedSupport
            depth n partAt rawTargets ambient).card : ℝ) +
          (ambient.card : ℝ) *
            WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) ySourceProfile k *
            WordType.conditionalFeatureEntropyPenaltyBase
              ySourceProfile yJointExponentPerRepetition ^ k +
          ((cwTotalWeightYIsolatedSupport
              depth n partAt rawTargets ambient).card : ℝ) *
            WordType.conditionalFeatureEntropyLoss
              (CWTotalWeightTaggedAtom depth Part) zSourceProfile k *
            WordType.conditionalFeatureEntropyPenaltyBase
              zSourceProfile zJointExponentPerRepetition ^ k := by
      gcongr
      · exact sum_address_card_cwTotalWeightYCompetitorFeatureClass_le
          depth n ySourceProfile k rawTargets ambient
          yJointExponentPerRepetition hyLength hyMass hk hySource
          hyFeatureSource hyExponent
      · exact sum_address_card_cwTotalWeightZCompetitorFeatureClass_le
          depth n zSourceProfile k rawTargets
          (cwTotalWeightYIsolatedSupport depth n partAt rawTargets ambient)
          zJointExponentPerRepetition hzLength hzMass hk hzSource
          hzFeatureSource hzExponent

end AlgebraicComplexity.Examples
