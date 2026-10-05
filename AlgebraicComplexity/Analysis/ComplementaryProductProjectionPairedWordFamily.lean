/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ComplementaryProductProjectionWordFamily
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrencePairedWordCore
import AlgebraicComplexity.Combinatorics.PooledMarginalProfileCore

/-!
# Integral pooled profiles for ordered-parent word-family counts

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*, fixes one fine block and counts compatible
ordered parent-state words.  At each parent position the two labelled child symbols stay paired,
and compatibility fixes only the sum of their two occurrence tables.

`ComplementaryProductProjectionWordFamily` proves the analytic count from normalized probability
equalities.  Concrete recursive clients, however, naturally produce exact integral profiles.
This module is the denominator-free adapter between those interfaces.  It normalizes the
multiplicity of the literal parent-pair word and proves that this law is exactly the product-swap
reindexing of the empirical `(fixed child pair, varying state)` law.

The public theorem therefore asks only for the existing memberwise predicate
`WordType.IsPooledMarginalProfile`.  It neither fixes the left and right occurrence tables
separately nor enlarges the supplied family to an ambient type class.  This formalizes the
fixed-fine numerator step of [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:388-436`, especially lines 402--429.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v w

private theorem mappedType_equiv_apply
    {A : Type u} {B : Type v} [Fintype A]
    (e : A ≃ B) (profile : A → ℕ) (b : B) :
    mappedType e profile b = profile (e.symm b) := by
  classical
  rw [mappedType_eq_sum_ite, Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ ha
    have hne : e a ≠ b := by
      intro h
      exact ha (e.injective (by simpa using h))
    simp [hne]
  · simp

private theorem normalizedProfileProbability_reindex_equiv
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) (profile : A → ℕ) (hmass : 0 < profileMass profile) :
    (normalizedProfileProbability profile hmass).reindex e =
      normalizedProfileProbability (mappedType e profile) (by
        simpa only [profileMass_mappedType] using hmass) := by
  apply ProbabilityVector.ext
  funext b
  rw [ProbabilityVector.reindex_weight,
    normalizedProfileProbability_weight,
    normalizedProfileProbability_weight,
    mappedType_equiv_apply,
    profileMass_mappedType]

private theorem normalizedJointWordProbability_reindex_prodComm_eq_parentPairWord
    {Symbol : Type u} {State : Type v}
    [Fintype Symbol] [Fintype State]
    {n : ℕ} (source : Fin n → Symbol × Symbol)
    (target : Fin n → State) (hn : 0 < n) :
    (normalizedJointWordProbability source target hn).reindex
        (Equiv.prodComm (Symbol × Symbol) State) =
      normalizedProfileProbability
        (multiplicity
          (ComplementaryOccurrenceLaw.parentPairWord target
            (fun i ↦ (source i).1) (fun i ↦ (source i).2))) (by
          simpa only [profileMass, sum_multiplicity] using hn) := by
  let e := Equiv.prodComm (Symbol × Symbol) State
  let joint := jointWord source target
  have hword :
      ComplementaryOccurrenceLaw.parentPairWord target
          (fun i ↦ (source i).1) (fun i ↦ (source i).2) =
        e ∘ joint := by
    rfl
  have hprofile :
      mappedType e (multiplicity joint) =
        multiplicity
          (ComplementaryOccurrenceLaw.parentPairWord target
            (fun i ↦ (source i).1) (fun i ↦ (source i).2)) := by
    rw [hword, multiplicity_comp_eq_mappedType]
  unfold normalizedJointWordProbability
  rw [normalizedProfileProbability_reindex_equiv]
  simp only [joint, e, hprofile]

/-- Count an actual family of ordered parent-state words from exact integral pooled profiles.

For each target, the profile in `hprofile` is the multiplicity of the literal parent-pair word
`(state, (left child, right child))`.  Its feasibility predicate enforces the reference's
structural zeros, fixes the state marginal and the sum of the two labelled occurrence marginals,
but does not fix those occurrence marginals separately.

Proof sketch: normalize the feasible integral profile.  The generic normalization theorem turns
it into a feasible probability law.  The private product-swap identity identifies that law with
the empirical law expected by the complementary-product actual-family theorem, which then gives
the stated count. -/
theorem
card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_pairedPooledProfile
    {Symbol : Type u} {State : Type v} {Cell : Type w}
    [Fintype Symbol] [Fintype State] [Fintype Cell]
    [DecidableEq Symbol] [DecidableEq State] [DecidableEq Cell]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (sourceProfile : Symbol × Symbol → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → Symbol × Symbol)
    (words : Finset (Fin (profileMass sourceProfile * k) → State))
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hprofile : ∀ target ∈ words,
      IsPooledMarginalProfile M.toSparsePooledMarginalProjectionModel
        (multiplicity
          (ComplementaryOccurrenceLaw.parentPairWord target
            (fun i ↦ (source i).1) (fun i ↦ (source i).2)))) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss State sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          ((profileMass sourceProfile : ℝ) * Real.log 2 *
            (M.stateLaw.entropyBits +
              ∑ state, M.stateLaw.weight state *
                ((M.childLaw (M.cellOf state)).entropyBits +
                  (M.childLaw (M.cellOf (M.complement state))).entropyBits))) ^ k := by
  apply
   card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_complementaryProductProjection
      M sourceProfile k source words hmass hk hsource
  intro target htarget
  let parentProfile :=
    multiplicity
      (ComplementaryOccurrenceLaw.parentPairWord target
        (fun i ↦ (source i).1) (fun i ↦ (source i).2))
  have hparentMass : 0 < profileMass parentProfile := by
    dsimp only [parentProfile]
    simpa only [profileMass, sum_multiplicity] using Nat.mul_pos hmass hk
  have hfeasible := normalizedProfileProbability_isPooledFeasible
    M.toSparsePooledMarginalProjectionModel parentProfile hparentMass
      (hprofile target htarget)
  have hreindex :=
    normalizedJointWordProbability_reindex_prodComm_eq_parentPairWord
      source target (Nat.mul_pos hmass hk)
  change
    let empirical :=
      (normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).reindex
        (Equiv.prodComm (Symbol × Symbol) State)
    empirical.pushforward M.coarse = M.reference.pushforward M.coarse ∧
      ∀ feature,
        (empirical.pushforward M.leftFeature).weight feature +
            (empirical.pushforward M.rightFeature).weight feature =
          (M.reference.pushforward M.leftFeature).weight feature +
            (M.reference.pushforward M.rightFeature).weight feature
  dsimp only
  rw [hreindex]
  simpa only [parentProfile, ComplementaryProductProjectionModel.coarse,
    ComplementaryProductProjectionModel.toSparsePooledMarginalProjectionModel_reference,
    ComplementaryProductProjectionModel.toSparsePooledMarginalProjectionModel_coarse,
    ComplementaryProductProjectionModel.toSparsePooledMarginalProjectionModel_leftFeature,
    ComplementaryProductProjectionModel.toSparsePooledMarginalProjectionModel_rightFeature] using
      hfeasible.2

private def pairedPooledTinyModel : ComplementaryProductProjectionModel Unit Unit Unit where
  stateLaw := ProbabilityVector.pointMass ()
  complement := Equiv.refl _
  cellOf := fun _ ↦ ()
  childLaw := fun _ ↦ ProbabilityVector.pointMass ()

private def pairedPooledTinyProfile : Unit × Unit → ℕ := fun _ ↦ 1

private def pairedPooledTinySource :
    Fin (profileMass pairedPooledTinyProfile * 1) → Unit × Unit :=
  fun _ ↦ ((), ())

private def pairedPooledTinyWords :
    Finset (Fin (profileMass pairedPooledTinyProfile * 1) → Unit) :=
  Finset.univ

private theorem pairedPooledTinyProfile_mass_pos :
    0 < profileMass pairedPooledTinyProfile := by
  simp [pairedPooledTinyProfile, profileMass, Finset.sum_const, Fintype.card_prod]

private theorem pairedPooledTinySource_multiplicity :
    WordType.multiplicity pairedPooledTinySource =
      proportionalCounts pairedPooledTinyProfile 1 := by
  classical
  funext pair
  have hpair : pair = ((), ()) := Subsingleton.elim _ _
  subst pair
  rw [show pairedPooledTinySource = fun _ ↦ ((), ()) by rfl, multiplicity_const]
  simp [pairedPooledTinyProfile, proportionalCounts, profileMass,
    Finset.sum_const, Fintype.card_prod]

private theorem pushforward_eq_pointMass_of_subsingleton
    {I O : Type} [Fintype I] [Fintype O] [DecidableEq O] [Subsingleton O]
    (p : ProbabilityVector I) (f : I → O) (o : O) :
    p.pushforward f = ProbabilityVector.pointMass o := by
  apply ProbabilityVector.pushforward_eq_pointMass_of_forall_weight_pos
  intro i _
  exact Subsingleton.elim (f i) o

private theorem pairedPooledTiny_parentProfile_isPooled
    (target : Fin (profileMass pairedPooledTinyProfile * 1) → Unit) :
    IsPooledMarginalProfile
      pairedPooledTinyModel.toSparsePooledMarginalProjectionModel
      (WordType.multiplicity
        (ComplementaryOccurrenceLaw.parentPairWord target
          (fun i ↦ (pairedPooledTinySource i).1)
          (fun i ↦ (pairedPooledTinySource i).2))) := by
  classical
  let profile := WordType.multiplicity
    (ComplementaryOccurrenceLaw.parentPairWord target
      (fun i ↦ (pairedPooledTinySource i).1)
      (fun i ↦ (pairedPooledTinySource i).2))
  have hmass : 0 < profileMass profile := by
    dsimp only [profile]
    rw [profileMass, sum_multiplicity]
    exact Nat.mul_pos pairedPooledTinyProfile_mass_pos Nat.zero_lt_one
  change IsPooledMarginalProfile
    pairedPooledTinyModel.toSparsePooledMarginalProjectionModel profile
  unfold IsPooledMarginalProfile
  refine ⟨?_, ?_, ?_⟩
  · intro sample hzero
    have hsample : sample = ((), ((), ())) := Subsingleton.elim _ _
    subst sample
    simp [pairedPooledTinyModel, ComplementaryProductProjectionModel.reference] at hzero
  · intro state
    have hstate : state = () := Subsingleton.elim _ _
    subst state
    have hmap := profileMass_mappedType
      pairedPooledTinyModel.toSparsePooledMarginalProjectionModel.coarse profile
    have hmap' :
        mappedType pairedPooledTinyModel.toSparsePooledMarginalProjectionModel.coarse profile () =
          profileMass profile := by
      simpa only [profileMass, Fintype.sum_unique] using hmap
    rw [hmap']
    simp [pairedPooledTinyModel, ComplementaryProductProjectionModel.reference,
      Nat.cast_ne_zero.mpr hmass.ne']
  · intro feature
    have hfeature : feature = ((), ()) := Subsingleton.elim _ _
    subst feature
    have hleft :
        mappedType pairedPooledTinyModel.toSparsePooledMarginalProjectionModel.leftFeature
            profile ((), ()) = profileMass profile := by
      rw [mappedType_eq_sum_ite]
      simp [pairedPooledTinyModel, profileMass]
    have hright :
        mappedType pairedPooledTinyModel.toSparsePooledMarginalProjectionModel.rightFeature
            profile ((), ()) = profileMass profile := by
      rw [mappedType_eq_sum_ite]
      simp [pairedPooledTinyModel, profileMass]
    rw [hleft, hright]
    rw [pushforward_eq_pointMass_of_subsingleton _ _ ((), ()),
      pushforward_eq_pointMass_of_subsingleton _ _ ((), ())]
    simp [Nat.cast_ne_zero.mpr hmass.ne']

/- This private application witnesses that every data-carrying hypothesis of the public theorem
can be instantiated simultaneously by a nonempty actual family. -/
private example :
    (pairedPooledTinyWords.card : ℝ) ≤
      conditionalFeatureEntropyLoss Unit pairedPooledTinyProfile 1 *
        conditionalFeatureEntropyPenaltyBase pairedPooledTinyProfile
          ((profileMass pairedPooledTinyProfile : ℝ) * Real.log 2 *
            (pairedPooledTinyModel.stateLaw.entropyBits +
              ∑ state, pairedPooledTinyModel.stateLaw.weight state *
                ((pairedPooledTinyModel.childLaw
                    (pairedPooledTinyModel.cellOf state)).entropyBits +
                  (pairedPooledTinyModel.childLaw
                    (pairedPooledTinyModel.cellOf
                      (pairedPooledTinyModel.complement state))).entropyBits))) ^ 1 := by
  apply
    card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_pairedPooledProfile
      pairedPooledTinyModel pairedPooledTinyProfile 1 pairedPooledTinySource
        pairedPooledTinyWords pairedPooledTinyProfile_mass_pos Nat.zero_lt_one
        pairedPooledTinySource_multiplicity
  intro target _
  exact pairedPooledTiny_parentProfile_isPooled target

end AlgebraicComplexity.WordType
