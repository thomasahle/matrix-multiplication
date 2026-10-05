/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalWordFamilyCoarsenedEntropy
import AlgebraicComplexity.Probability.ComplementaryProductProjection
import AlgebraicComplexity.Probability.ReindexBasic

/-!
# Actual-family counts from a complementary-product projection

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*, fixes a paired fine block and counts the
ordered parent-state words compatible with it.  Its constraint fixes the ordered-state marginal
and the *sum* of the two labelled child-occurrence marginals; it does not fix the left and right
tables separately.

This module connects that pooled constraint to the existing actual-family method of types.  The
fixed word has letters `(left child, right child)`, while a varying word records one ordered state
per parent position.  Swapping the normalized empirical joint law puts it in the
`ComplementaryProductProjectionModel` convention.  The pooled information projection bounds the
entropy of the child pair conditional on the state, and the ordinary conditional-word theorem
then subtracts the entropy of the fixed paired fine profile exactly once.

Thus the exponential numerator rate is

`H(state) + H(left child, right child | state) - H(fixed paired fine profile)`.

The theorem is an actual-family bound: feasibility is required only for words in the supplied
finset.  It defines no compatibility relation and assumes no separately labelled occurrence
tables.  Concrete Total-Weight clients must still prove that their literal compatibility fiber
has the displayed pooled empirical laws.  This formalizes the fixed-fine numerator step of
[alman2025more, Claim 6.18], `papers/sources/2404.16349/constituent.tex:388-436`, especially
lines 402--429.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v w

/-- Count an arbitrary family of ordered parent-state words from the complementary-product
projection satisfied by each realized empirical law.

The source word consists of paired child symbols.  For a target state word, `empirical` is the
normalized joint law after swapping `(child pair, state)` to `(state, child pair)`.  The two
hypotheses in `hprojection` say exactly that `empirical` has the reference state marginal and the
reference *pooled* labelled-occurrence marginal.

Proof sketch: the state-marginal equality fixes the target entropy at `H(M.stateLaw)`.  Apply the
pooled information-projection inequality to bound the entropy of the paired child symbol
conditional on the state by the displayed weighted sum of child-law entropies.  Reindexing by
product commutation preserves entropy and turns that conditional entropy into the coarsened
conditional term expected by the actual-family counting theorem. -/
theorem
card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_complementaryProductProjection
    {Symbol : Type u} {State : Type v} {Cell : Type w}
    [Fintype Symbol] [Fintype State] [Fintype Cell]
    [DecidableEq Symbol] [DecidableEq State] [DecidableEq Cell]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (sourceProfile : Symbol × Symbol → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → Symbol × Symbol)
    (words : Finset (Fin (profileMass sourceProfile * k) → State))
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hprojection : ∀ target ∈ words,
      let empirical :=
        (normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).reindex
          (Equiv.prodComm (Symbol × Symbol) State)
      empirical.pushforward M.coarse = M.reference.pushforward M.coarse ∧
        ∀ feature,
          (empirical.pushforward M.leftFeature).weight feature +
              (empirical.pushforward M.rightFeature).weight feature =
            (M.reference.pushforward M.leftFeature).weight feature +
              (M.reference.pushforward M.rightFeature).weight feature) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss State sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          ((profileMass sourceProfile : ℝ) * Real.log 2 *
            (M.stateLaw.entropyBits +
              ∑ state, M.stateLaw.weight state *
                ((M.childLaw (M.cellOf state)).entropyBits +
                  (M.childLaw (M.cellOf (M.complement state))).entropyBits))) ^ k := by
  let conditionalUpper :=
    ∑ state, M.stateLaw.weight state *
      ((M.childLaw (M.cellOf state)).entropyBits +
        (M.childLaw (M.cellOf (M.complement state))).entropyBits)
  apply card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coarsenedBounds
    sourceProfile k source words id M.stateLaw.entropyBits conditionalUpper
      hmass hk hsource
  · intro target htarget
    let joint := normalizedJointWordProbability source target (Nat.mul_pos hmass hk)
    let empirical := joint.reindex (Equiv.prodComm (Symbol × Symbol) State)
    have hdata := hprojection target htarget
    have hstate : empirical.pushforward M.coarse = M.stateLaw := by
      calc
        empirical.pushforward M.coarse = M.reference.pushforward M.coarse := hdata.1
        _ = M.stateLaw := M.reference_pushforward_coarse
    have hswap :
        empirical.pushforward M.coarse = joint.pushforward Prod.snd := by
      dsimp only [empirical]
      rw [ProbabilityVector.pushforward_reindex]
      congr 1
    rw [← hswap, hstate]
  · intro target htarget
    let joint := normalizedJointWordProbability source target (Nat.mul_pos hmass hk)
    let empirical := joint.reindex (Equiv.prodComm (Symbol × Symbol) State)
    have hdata := hprojection target htarget
    have hprojectionBound :=
      M.conditionalEntropyBits_add_parentKlBits_le M.coarse empirical hdata.1 hdata.2
    have habsolutelyContinuous :=
      M.isAbsolutelyContinuous_of_coarse_eq_of_pooledFeature_eq empirical hdata.1 hdata.2
    have hklNats := ProbabilityVector.klDiv_nonneg_of_absoluteContinuity
      (empirical.pushforward M.coarse) (M.reference.pushforward M.coarse)
      (habsolutelyContinuous.pushforward M.coarse)
    have hklBits : 0 ≤
        (empirical.pushforward M.coarse).klDivBits
          (M.reference.pushforward M.coarse) := by
      exact div_nonneg hklNats (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hconditional :
        empirical.conditionalEntropyBits M.coarse ≤ conditionalUpper := by
      linarith
    have hidentity :
        joint.pushforward (fun entry ↦ (entry.1, id entry.2)) = joint := by
      calc
        joint.pushforward (fun entry ↦ (entry.1, id entry.2)) =
            joint.pushforward (Equiv.refl _) := by
          congr 1
        _ = joint.reindex (Equiv.refl _) :=
          (ProbabilityVector.reindex_eq_pushforward (Equiv.refl _) joint).symm
        _ = joint := by
          apply ProbabilityVector.ext
          funext entry
          simp
    have hswap :
        empirical.pushforward M.coarse = joint.pushforward Prod.snd := by
      dsimp only [empirical]
      rw [ProbabilityVector.pushforward_reindex]
      congr 1
    have hconditionalReindex :
        joint.conditionalEntropyBits Prod.snd =
          empirical.conditionalEntropyBits M.coarse := by
      unfold ProbabilityVector.conditionalEntropyBits ProbabilityVector.conditionalEntropy
      rw [hswap]
      dsimp only [empirical]
      rw [ProbabilityVector.entropy_reindex]
    rw [hidentity, hconditionalReindex]
    exact hconditional

/-! The singleton model below verifies that every data-carrying binder of the public theorem can
be instantiated simultaneously for a nonempty actual family. -/

private theorem uniqueProbabilityVector_ext
    {I : Type} [Fintype I] [Unique I]
    (p q : ProbabilityVector I) : p = q := by
  apply ProbabilityVector.ext
  funext i
  have hi : i = default := Unique.eq_default i
  subst i
  have hp : p.weight default = 1 := by
    simpa only [Fintype.sum_unique] using p.total
  have hq : q.weight default = 1 := by
    simpa only [Fintype.sum_unique] using q.total
  rw [hp, hq]

private def tinyComplementaryProductModel :
    ComplementaryProductProjectionModel Unit Unit Unit where
  stateLaw := ProbabilityVector.pointMass ()
  complement := Equiv.refl _
  cellOf := fun _ ↦ ()
  childLaw := fun _ ↦ ProbabilityVector.pointMass ()

private def tinyPairedProfile : Unit × Unit → ℕ := fun _ ↦ 1

private def tinyPairedSource :
    Fin (profileMass tinyPairedProfile * 1) → Unit × Unit :=
  fun _ ↦ ((), ())

private def tinyParentWords :
    Finset (Fin (profileMass tinyPairedProfile * 1) → Unit) :=
  Finset.univ

private theorem tinyPairedSource_multiplicity :
    WordType.multiplicity tinyPairedSource =
      proportionalCounts tinyPairedProfile 1 := by
  classical
  funext pair
  have hpair : pair = ((), ()) := Subsingleton.elim _ _
  subst pair
  rw [show tinyPairedSource = fun _ ↦ ((), ()) by rfl, multiplicity_const]
  simp [tinyPairedProfile, proportionalCounts, profileMass, Finset.sum_const]

private theorem tinyParentWords_nonempty : tinyParentWords.Nonempty := by
  exact ⟨fun _ ↦ (), Finset.mem_univ _⟩

/-- Binder-level satisfiability check for the pooled actual-family theorem. -/
private example :
    (tinyParentWords.card : ℝ) ≤
      conditionalFeatureEntropyLoss Unit tinyPairedProfile 1 *
        conditionalFeatureEntropyPenaltyBase tinyPairedProfile
          ((profileMass tinyPairedProfile : ℝ) * Real.log 2 *
            (tinyComplementaryProductModel.stateLaw.entropyBits +
              ∑ state, tinyComplementaryProductModel.stateLaw.weight state *
                ((tinyComplementaryProductModel.childLaw
                    (tinyComplementaryProductModel.cellOf state)).entropyBits +
                  (tinyComplementaryProductModel.childLaw
                    (tinyComplementaryProductModel.cellOf
                      (tinyComplementaryProductModel.complement state))).entropyBits))) ^ 1 := by
  letI : Unique (Unit × Unit) := {
    default := ((), ())
    uniq _ := Subsingleton.elim _ _
  }
  have _hnonempty := tinyParentWords_nonempty
  refine
   card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_complementaryProductProjection
      tinyComplementaryProductModel tinyPairedProfile 1 tinyPairedSource tinyParentWords
      (by simp [tinyPairedProfile, profileMass]) (by norm_num)
      tinyPairedSource_multiplicity ?_
  intro target _htarget
  dsimp only
  constructor
  · exact uniqueProbabilityVector_ext _ _
  · intro feature
    have hleft :
        (((normalizedJointWordProbability tinyPairedSource target (by
            simp [tinyPairedProfile, profileMass])).reindex
              (Equiv.prodComm (Unit × Unit) Unit)).pushforward
                tinyComplementaryProductModel.leftFeature) =
          tinyComplementaryProductModel.reference.pushforward
            tinyComplementaryProductModel.leftFeature :=
      uniqueProbabilityVector_ext _ _
    have hright :
        (((normalizedJointWordProbability tinyPairedSource target (by
            simp [tinyPairedProfile, profileMass])).reindex
              (Equiv.prodComm (Unit × Unit) Unit)).pushforward
                tinyComplementaryProductModel.rightFeature) =
          tinyComplementaryProductModel.reference.pushforward
            tinyComplementaryProductModel.rightFeature :=
      uniqueProbabilityVector_ext _ _
    rw [hleft, hright]

end AlgebraicComplexity.WordType
