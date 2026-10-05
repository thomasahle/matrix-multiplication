/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalWordFamilyEntropyGrowth
import AlgebraicComplexity.Combinatorics.PooledMarginalProfileCore
import AlgebraicComplexity.Probability.PooledMarginalProjection

/-!
# Actual-family counts from a sparse pooled projection

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*, fixes one physical fine word and counts the
ordered parent words compatible with it.  In a recursive construction, the feature read from a
fine symbol may depend on the competing parent state.  The relevant empirical alphabet is then
the literal product `Raw × State`; replacing the raw word by a candidate-independent quotient is
not sound in general.

This module supplies the paper-independent counting bridge for that situation.  A sparse pooled
projection model may use arbitrary left and right feature maps on `Raw × State`, while its coarse
statistic is required to be the physical raw coordinate.  If every actually realized joint type
is feasible for the model, the information-projection inequality bounds its conditional entropy
`H(State | Raw)`.  The arbitrary-family method of types then bounds the number of candidate words.

This formalizes the fixed-fine maximum-entropy step in [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:388-436`, especially lines 402--429.  It introduces no
compatibility relation, tensor, CW alphabet, asymptotic limit, or numerical certificate.
-/

set_option autoImplicit false

namespace AlgebraicComplexity
namespace WordType

universe u v w

/-- Count an arbitrary family of candidate words using a sparse pooled projection on the literal
joint alphabet `Raw × State`.

The source word has one fixed proportional raw type.  For every candidate in `words`, `hprofile`
requires the exact empirical joint type to have the reference support, the reference raw marginal,
and the reference sum of the two feature marginals.  The feature maps belong to `M` and may depend
on both the raw letter and the candidate state.

Proof sketch: normalize each realized integral joint profile.  Exact integral feasibility becomes
probability-vector feasibility.  Sparse pooled information projection and nonnegativity of KL give
`H(State | Raw) ≤ H_M(State | Raw)`.  Rewriting the normalized raw marginal using `hsource` turns
this into the profile-conditional entropy premise of the arbitrary-family method-of-types theorem.
-/
theorem
card_words_le_conditionalFeatureEntropyLoss_mul_profileConditionalEntropyBitsBase_pow_of_pooledMarginalProjection
    {Raw : Type u} {State : Type v} {Feature : Type w}
    [Fintype Raw] [Fintype State] [Fintype Feature]
    [DecidableEq Raw] [DecidableEq State] [DecidableEq Feature]
    (M : SparsePooledMarginalProjectionModel (Raw × State) Raw Feature)
    (hcoarse : M.coarse = Prod.fst)
    (sourceProfile : Raw → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → Raw)
    (words : Finset (Fin (profileMass sourceProfile * k) → State))
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hprofile : ∀ target ∈ words,
      IsPooledMarginalProfile M (multiplicity (jointWord source target))) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss State sourceProfile k *
        (Real.exp
          ((profileMass sourceProfile : ℝ) * Real.log 2 *
            M.reference.conditionalEntropyBits M.coarse)) ^ k := by
  apply card_words_le_conditionalFeatureEntropyLoss_mul_profileConditionalEntropyBitsBase_pow
    sourceProfile k source words
      (M.reference.conditionalEntropyBits M.coarse) hmass hk hsource
  intro target htarget
  let jointProfile := multiplicity (jointWord source target)
  have hjointMass : profileMass jointProfile = profileMass sourceProfile * k := by
    simpa only [jointProfile, profileMass] using
      (sum_multiplicity (jointWord source target))
  have hjointMassPos : 0 < profileMass jointProfile := by
    rw [hjointMass]
    exact Nat.mul_pos hmass hk
  let empirical := normalizedProfileProbability jointProfile hjointMassPos
  have hempiricalFeasible : M.IsFeasible empirical := by
    exact normalizedProfileProbability_isPooledFeasible M jointProfile hjointMassPos
      (hprofile target htarget)
  have hprojection :=
    M.conditionalEntropyBits_add_parentQuadratic_le
      M.coarse empirical hempiricalFeasible
  have hquadratic :
      0 ≤ (empirical.pushforward M.coarse).quadraticKlLowerBits
        (M.reference.pushforward M.coarse) := by
    unfold ProbabilityVector.quadraticKlLowerBits
    exact div_nonneg
      (ProbabilityVector.quadraticKlLower_nonneg
        (empirical.pushforward M.coarse) (M.reference.pushforward M.coarse))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hempiricalConditional :
      empirical.conditionalEntropyBits M.coarse ≤
        M.reference.conditionalEntropyBits M.coarse := by
    linarith
  have hmap : mappedType Prod.fst jointProfile = proportionalCounts sourceProfile k := by
    calc
      mappedType Prod.fst jointProfile = multiplicity source := by
        rw [show jointProfile = multiplicity (jointWord source target) by rfl]
        rw [← multiplicity_comp_eq_mappedType]
        rfl
      _ = proportionalCounts sourceProfile k := hsource
  have hpush :
      empirical.pushforward Prod.fst =
        normalizedProfileProbability sourceProfile hmass := by
    apply ProbabilityVector.ext
    funext raw
    dsimp only [empirical]
    rw [normalizedProfileProbability_pushforward_weight,
      normalizedProfileProbability_weight, congrFun hmap raw, hjointMass]
    simp only [proportionalCounts, Nat.cast_mul]
    exact mul_div_mul_right (sourceProfile raw : ℝ) (profileMass sourceProfile : ℝ)
      (by exact_mod_cast hk.ne')
  have hempiricalConditionalFst :
      empirical.conditionalEntropyBits Prod.fst ≤
        M.reference.conditionalEntropyBits M.coarse := by
    simpa only [hcoarse] using hempiricalConditional
  have hempiricalConditionalEq :
      empirical.conditionalEntropyBits Prod.fst =
        (profileEntropyNats jointProfile - profileEntropyNats sourceProfile) /
          Real.log 2 := by
    unfold ProbabilityVector.conditionalEntropyBits
      ProbabilityVector.conditionalEntropy
    rw [show empirical.entropy = profileEntropyNats jointProfile by
          exact normalizedProfileProbability_entropy jointProfile hjointMassPos,
      hpush,
      normalizedProfileProbability_entropy sourceProfile hmass]
  rw [hempiricalConditionalEq] at hempiricalConditionalFst
  simpa only [jointProfile] using hempiricalConditionalFst

/-! The private singleton below instantiates every data-carrying binder with a nonempty family. -/

private def pooledWordTinyModel :
    SparsePooledMarginalProjectionModel (Unit × Unit) Unit Unit where
  reference := ProbabilityVector.pointMass ((), ())
  coarse := Prod.fst
  leftFeature := fun _ ↦ ()
  rightFeature := fun _ ↦ ()
  coarsePotential := fun _ ↦ 0
  featurePotential := fun _ ↦ 0
  log_reference_weight := by
    intro sample _hsample
    have hsample : sample = ((), ()) := Subsingleton.elim _ _
    subst sample
    simp

private def pooledWordTinySourceProfile : Unit → ℕ := fun _ ↦ 1

private def pooledWordTinySource :
    Fin (profileMass pooledWordTinySourceProfile * 1) → Unit := fun _ ↦ ()

private def pooledWordTinyWords :
    Finset (Fin (profileMass pooledWordTinySourceProfile * 1) → Unit) :=
  Finset.univ

private theorem pooledWordTinySourceProfile_mass_pos :
    0 < profileMass pooledWordTinySourceProfile := by
  simp [pooledWordTinySourceProfile, profileMass]

private theorem pooledWordTinySource_multiplicity :
    multiplicity pooledWordTinySource =
      proportionalCounts pooledWordTinySourceProfile 1 := by
  classical
  funext raw
  have hraw : raw = () := Subsingleton.elim _ _
  subst raw
  rw [show pooledWordTinySource = fun _ ↦ () by rfl, multiplicity_const]
  simp [pooledWordTinySourceProfile, proportionalCounts, profileMass]

private theorem pooledWordTiny_isPooled
    (target : Fin (profileMass pooledWordTinySourceProfile * 1) → Unit) :
    IsPooledMarginalProfile pooledWordTinyModel
      (multiplicity (jointWord pooledWordTinySource target)) := by
  classical
  let jointProfile := multiplicity (jointWord pooledWordTinySource target)
  have hjointMass : profileMass jointProfile = 1 := by
    dsimp only [jointProfile]
    rw [profileMass, sum_multiplicity]
    simp [pooledWordTinySourceProfile, profileMass]
  unfold IsPooledMarginalProfile
  refine ⟨?_, ?_, ?_⟩
  · intro sample hzero
    have hsample : sample = ((), ()) := Subsingleton.elim _ _
    subst sample
    simp [pooledWordTinyModel] at hzero
  · intro raw
    have hraw : raw = () := Subsingleton.elim _ _
    subst raw
    have hmap' : mappedType pooledWordTinyModel.coarse jointProfile () = 1 := by
      calc
        mappedType pooledWordTinyModel.coarse jointProfile () =
            profileMass jointProfile := by
          rw [mappedType_eq_sum_ite]
          simp [pooledWordTinyModel, profileMass]
        _ = 1 := hjointMass
    rw [hmap', hjointMass]
    simp [pooledWordTinyModel]
  · intro feature
    have hfeature : feature = () := Subsingleton.elim _ _
    subst feature
    have hleft' : mappedType pooledWordTinyModel.leftFeature jointProfile () = 1 := by
      calc
        mappedType pooledWordTinyModel.leftFeature jointProfile () =
            profileMass jointProfile := by
          rw [mappedType_eq_sum_ite]
          simp [pooledWordTinyModel, profileMass]
        _ = 1 := hjointMass
    have hright' : mappedType pooledWordTinyModel.rightFeature jointProfile () = 1 := by
      calc
        mappedType pooledWordTinyModel.rightFeature jointProfile () =
            profileMass jointProfile := by
          rw [mappedType_eq_sum_ite]
          simp [pooledWordTinyModel, profileMass]
        _ = 1 := hjointMass
    rw [hleft', hright', hjointMass]
    simp [pooledWordTinyModel]

private example : pooledWordTinyWords.Nonempty ∧
    (pooledWordTinyWords.card : ℝ) ≤
      conditionalFeatureEntropyLoss Unit pooledWordTinySourceProfile 1 *
        (Real.exp
          ((profileMass pooledWordTinySourceProfile : ℝ) * Real.log 2 *
            pooledWordTinyModel.reference.conditionalEntropyBits
              pooledWordTinyModel.coarse)) ^ 1 := by
  constructor
  · exact ⟨fun _ ↦ (), by simp [pooledWordTinyWords]⟩
  · apply
      card_words_le_conditionalFeatureEntropyLoss_mul_profileConditionalEntropyBitsBase_pow_of_pooledMarginalProjection
        pooledWordTinyModel rfl pooledWordTinySourceProfile 1 pooledWordTinySource
          pooledWordTinyWords pooledWordTinySourceProfile_mass_pos Nat.zero_lt_one
          pooledWordTinySource_multiplicity
    intro target _htarget
    exact pooledWordTiny_isPooled target

end WordType
end AlgebraicComplexity
