/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalWordFamilyCoarsenedEntropy
import AlgebraicComplexity.Probability.PairedConditionalEntropy
import AlgebraicComplexity.Probability.ReindexBasic

/-!
# Paired coarsened-entropy bounds for empirical word families

The proof of Claim 6.18 in Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*
(`papers/sources/2404.16349/constituent.tex`, lines 404--432), partitions a compatibility word
into exact and pooled cells and counts the possibilities on those cells.  This module supplies a
paper-independent auxiliary entropy bound used by the occurrence formulation of that count:
separate conditional-entropy ceilings for the two source coordinates add to a ceiling for their
pair after both target cells are revealed.

The proof rebrackets the empirical law as a coupling of `(left source, left cell)` and
`(right source, right cell)`, applies conditional-entropy subadditivity, and feeds the result to
the existing actual-family word count.  In particular, the theorem never enlarges the supplied
finite family of target words to an ambient type class.  This is the semantic point required by
the Total-Weight manuscript's quotient-feature condition (`better_bound/paper.tex`, lines
1750--1792).

No tensor, CW alphabet, certificate constant, or generated datum occurs here.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.WordType

universe u v w x y

/-- Separate conditional-entropy bounds for the two coordinates of a paired source alphabet
give an actual-family word count with the two losses added.

More precisely, let the fixed source word take values in `D × E`.  For every target word in
`words`, suppose its visible target law has entropy at most `targetUpper`, the empirical `D`
coordinate has conditional entropy at most `leftUpper` after revealing `leftCell`, and the
empirical `E` coordinate has conditional entropy at most `rightUpper` after revealing
`rightCell`.  Then the joint type exponent is bounded by

`profileMass sourceProfile * log 2 * (targetUpper + leftUpper + rightUpper)`.

Proof sketch: push the normalized empirical law forward to
`(D × C) × (E × F)`.  It is a coupling of its coordinate marginals, so
`pairConditionalEntropyBits_le_add` bounds the entropy remaining after both cells are exposed by
the sum of the two assumed one-coordinate bounds.  A finite equivalence rebrackets this law as
`(D × E) × (C × F)`.  The ordinary coarsened actual-family theorem then supplies the
cardinality bound. -/
theorem card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_pairedCoarsenedBounds
    {D : Type u} {E : Type v} {T : Type w} {C : Type x} {F : Type y}
    [Fintype D] [Fintype E] [Fintype T] [Fintype C] [Fintype F]
    [DecidableEq D] [DecidableEq E] [DecidableEq T] [DecidableEq C] [DecidableEq F]
    (sourceProfile : D × E → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → D × E)
    (words : Finset (Fin (profileMass sourceProfile * k) → T))
    (leftCell : T → C) (rightCell : T → F)
    (targetUpper leftUpper rightUpper : ℝ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (htarget : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).pushforward
        Prod.snd).entropyBits ≤ targetUpper)
    (hleft : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).pushforward
        (fun st ↦ (st.1.1, leftCell st.2))).conditionalEntropyBits Prod.snd ≤
          leftUpper)
    (hright : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).pushforward
        (fun st ↦ (st.1.2, rightCell st.2))).conditionalEntropyBits Prod.snd ≤
          rightUpper) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss T sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          ((profileMass sourceProfile : ℝ) * Real.log 2 *
            (targetUpper + leftUpper + rightUpper)) ^ k := by
  classical
  let combinedCell : T → C × F := fun t ↦ (leftCell t, rightCell t)
  have hcombined : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).pushforward
        (fun st ↦ (st.1, combinedCell st.2))).conditionalEntropyBits Prod.snd ≤
          leftUpper + rightUpper := by
    intro target htargetMem
    let joint := normalizedJointWordProbability source target (Nat.mul_pos hmass hk)
    let paired : ProbabilityVector ((D × C) × (E × F)) :=
      joint.pushforward fun st ↦
        ((st.1.1, leftCell st.2), (st.1.2, rightCell st.2))
    have hpair :
        paired.conditionalEntropyBits
            (fun de ↦ (de.1.2, de.2.2)) ≤
          (paired.pushforward Prod.fst).conditionalEntropyBits Prod.snd +
            (paired.pushforward Prod.snd).conditionalEntropyBits Prod.snd :=
      (ProbabilityVector.IsCoupling.marginals paired).pairConditionalEntropyBits_le_add
        Prod.snd Prod.snd
    have hleft' :
        (paired.pushforward Prod.fst).conditionalEntropyBits Prod.snd ≤ leftUpper := by
      have hleftLaw :
          paired.pushforward Prod.fst =
            joint.pushforward (fun st ↦ (st.1.1, leftCell st.2)) := by
        dsimp only [paired]
        rw [ProbabilityVector.pushforward_comp]
        rfl
      rw [hleftLaw]
      exact hleft target htargetMem
    have hright' :
        (paired.pushforward Prod.snd).conditionalEntropyBits Prod.snd ≤ rightUpper := by
      have hrightLaw :
          paired.pushforward Prod.snd =
            joint.pushforward (fun st ↦ (st.1.2, rightCell st.2)) := by
        dsimp only [paired]
        rw [ProbabilityVector.pushforward_comp]
        rfl
      rw [hrightLaw]
      exact hright target htargetMem
    have hpairedBound :
        paired.conditionalEntropyBits (fun de ↦ (de.1.2, de.2.2)) ≤
          leftUpper + rightUpper :=
      hpair.trans (add_le_add hleft' hright')
    let regroup : ((D × C) × (E × F)) ≃ ((D × E) × (C × F)) := {
      toFun de := ((de.1.1, de.2.1), (de.1.2, de.2.2))
      invFun de := ((de.1.1, de.2.1), (de.1.2, de.2.2))
      left_inv de := by
        rcases de with ⟨⟨d, c⟩, ⟨e, f⟩⟩
        rfl
      right_inv de := by
        rcases de with ⟨⟨d, e⟩, ⟨c, f⟩⟩
        rfl
    }
    have hregroup :
        paired.reindex regroup =
          joint.pushforward (fun st ↦ (st.1, combinedCell st.2)) := by
      rw [ProbabilityVector.reindex_eq_pushforward,
        ProbabilityVector.pushforward_comp]
      rfl
    have hconditionalEq :
        (joint.pushforward
            (fun st ↦ (st.1, combinedCell st.2))).conditionalEntropyBits Prod.snd =
          paired.conditionalEntropyBits (fun de ↦ (de.1.2, de.2.2)) := by
      rw [← hregroup]
      unfold ProbabilityVector.conditionalEntropyBits ProbabilityVector.conditionalEntropy
      rw [ProbabilityVector.entropy_reindex, ProbabilityVector.pushforward_reindex]
      rfl
    change
      (joint.pushforward
          (fun st ↦ (st.1, combinedCell st.2))).conditionalEntropyBits Prod.snd ≤
        leftUpper + rightUpper
    rw [hconditionalEq]
    exact hpairedBound
  simpa only [combinedCell, add_assoc] using
    card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coarsenedBounds
      sourceProfile k source words combinedCell targetUpper (leftUpper + rightUpper)
        hmass hk hsource htarget hcombined

/-! The following private regression checks that the theorem's data-carrying hypotheses are
simultaneously satisfiable.  All five alphabets are singletons, the profile has mass one, and the
target family contains one word.  Thus this is a genuine nonempty instance rather than an empty
family making the counting conclusion vacuous.  The definitions are kept unexpanded during the final
theorem application so this check does not ask the elaborator to normalize the entropy bound. -/

private def pairedTinyProfile : Unit × Unit → ℕ := fun _ ↦ 1

private def pairedTinySource : Fin (profileMass pairedTinyProfile * 1) → Unit × Unit :=
  fun _ ↦ ((), ())

private def pairedTinyTarget : Fin (profileMass pairedTinyProfile * 1) → Unit :=
  fun _ ↦ ()

private def pairedTinyWords : Finset (Fin (profileMass pairedTinyProfile * 1) → Unit) :=
  {pairedTinyTarget}

private theorem pairedTinyProfile_mass_pos : 0 < profileMass pairedTinyProfile := by
  simp [pairedTinyProfile, profileMass, Finset.sum_const, Fintype.card_prod]

private theorem pairedTinySource_multiplicity :
    multiplicity pairedTinySource = proportionalCounts pairedTinyProfile 1 := by
  classical
  funext de
  have hde : de = ((), ()) := Subsingleton.elim _ _
  subst de
  rw [show pairedTinySource = fun _ ↦ ((), ()) by rfl,
    multiplicity_const]
  simp [pairedTinyProfile, proportionalCounts, profileMass,
    Finset.sum_const, Fintype.card_prod]

private theorem pushforward_eq_pointMass_of_subsingleton
    {I O : Type} [Fintype I] [Fintype O] [DecidableEq O] [Subsingleton O]
    (p : ProbabilityVector I) (f : I → O) (o : O) :
    p.pushforward f = ProbabilityVector.pointMass o := by
  apply ProbabilityVector.pushforward_eq_pointMass_of_forall_weight_pos
  intro i _
  exact Subsingleton.elim (f i) o

private theorem pairedTinyTarget_entropy : ∀ candidate ∈ pairedTinyWords,
    ((normalizedJointWordProbability pairedTinySource candidate
        (Nat.mul_pos pairedTinyProfile_mass_pos Nat.zero_lt_one)).pushforward
      Prod.snd).entropyBits ≤ 0 := by
  intro candidate _
  have hpoint :
      (normalizedJointWordProbability pairedTinySource candidate
          (Nat.mul_pos pairedTinyProfile_mass_pos Nat.zero_lt_one)).pushforward Prod.snd =
        ProbabilityVector.pointMass () :=
    pushforward_eq_pointMass_of_subsingleton _ _ ()
  rw [hpoint]
  simp

private theorem pairedTinyLeft_conditionalEntropy : ∀ candidate ∈ pairedTinyWords,
    ((normalizedJointWordProbability pairedTinySource candidate
        (Nat.mul_pos pairedTinyProfile_mass_pos Nat.zero_lt_one)).pushforward
      (fun st ↦ (st.1.1, ()))).conditionalEntropyBits Prod.snd ≤ 0 := by
  intro candidate _
  have hpoint :
      (normalizedJointWordProbability pairedTinySource candidate
          (Nat.mul_pos pairedTinyProfile_mass_pos Nat.zero_lt_one)).pushforward
          (fun st ↦ (st.1.1, ())) =
        ProbabilityVector.pointMass ((), ()) :=
    pushforward_eq_pointMass_of_subsingleton _ _ ((), ())
  rw [hpoint]
  simp [ProbabilityVector.conditionalEntropyBits, ProbabilityVector.conditionalEntropy]

private theorem pairedTinyRight_conditionalEntropy : ∀ candidate ∈ pairedTinyWords,
    ((normalizedJointWordProbability pairedTinySource candidate
        (Nat.mul_pos pairedTinyProfile_mass_pos Nat.zero_lt_one)).pushforward
      (fun st ↦ (st.1.2, ()))).conditionalEntropyBits Prod.snd ≤ 0 := by
  intro candidate _
  have hpoint :
      (normalizedJointWordProbability pairedTinySource candidate
          (Nat.mul_pos pairedTinyProfile_mass_pos Nat.zero_lt_one)).pushforward
          (fun st ↦ (st.1.2, ())) =
        ProbabilityVector.pointMass ((), ()) :=
    pushforward_eq_pointMass_of_subsingleton _ _ ((), ())
  rw [hpoint]
  simp [ProbabilityVector.conditionalEntropyBits, ProbabilityVector.conditionalEntropy]

private example :
    (pairedTinyWords.card : ℝ) ≤
      conditionalFeatureEntropyLoss Unit pairedTinyProfile 1 *
        conditionalFeatureEntropyPenaltyBase pairedTinyProfile
          ((profileMass pairedTinyProfile : ℝ) * Real.log 2 *
            ((0 : ℝ) + 0 + 0)) ^ 1 := by
  exact
    card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_pairedCoarsenedBounds
      pairedTinyProfile 1 pairedTinySource pairedTinyWords
      (fun _ : Unit ↦ ()) (fun _ : Unit ↦ ())
      0 0 0 pairedTinyProfile_mass_pos Nat.zero_lt_one pairedTinySource_multiplicity
      pairedTinyTarget_entropy pairedTinyLeft_conditionalEntropy
      pairedTinyRight_conditionalEntropy

end AlgebraicComplexity.WordType
