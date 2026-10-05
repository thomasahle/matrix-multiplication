import AlgebraicComplexity.Analysis.ConditionalWordFamilyEntropyGrowth
import AlgebraicComplexity.Probability.CoarsenedConditionalEntropy

/-!
# Coarsened entropy bounds for empirical word families

The generic conditional word-family count requires a mass-weighted joint-entropy ceiling in
natural logarithms.  Certificate calculations more naturally bound two normalized quantities in
bits: the target entropy and the source entropy conditional on a deterministic target feature.

This module connects those interfaces.  It normalizes the empirical joint type of a pair of words,
applies data processing in the form
`H(S,T) ≤ H(T) + H(S | coarse(T))`, restores the integral profile mass and converts bits to nats.
The sequence-facing theorem then supplies exactly the witness-local premise of
`card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow`.

No particular alphabet, compatibility relation, tensor, certificate, or generated datum occurs
here.  The two normalized entropy ceilings remain explicit inputs for concrete clients.
-/

namespace AlgebraicComplexity.WordType

universe u v w

/-- The normalized empirical joint law of two positive-length words. -/
noncomputable def normalizedJointWordProbability
    {S : Type u} {T : Type v} [Fintype S] [Fintype T]
    {n : ℕ} (source : Fin n → S) (target : Fin n → T) (hn : 0 < n) :
    ProbabilityVector (S × T) :=
  normalizedProfileProbability (multiplicity (jointWord source target)) (by
    simpa only [profileMass, sum_multiplicity] using hn)

/-- Entropy of the normalized empirical joint law is the profile entropy of the joint type. -/
theorem normalizedJointWordProbability_entropy
    {S : Type u} {T : Type v} [Fintype S] [Fintype T]
    {n : ℕ} (source : Fin n → S) (target : Fin n → T) (hn : 0 < n) :
    (normalizedJointWordProbability source target hn).entropy =
      profileEntropyNats (multiplicity (jointWord source target)) := by
  unfold normalizedJointWordProbability
  exact normalizedProfileProbability_entropy _ _

/-- Two normalized entropy ceilings in bits give the corresponding mass-weighted empirical
joint-entropy ceiling in nats. -/
theorem profileMass_mul_profileEntropyNats_le_logTwo_mul_add_of_coarsenedBounds
    {S : Type u} {T : Type v} {C : Type w}
    [Fintype S] [Fintype T] [Fintype C]
    [DecidableEq S] [DecidableEq T] [DecidableEq C]
    (jointProfile : S × T → ℕ) (hmass : 0 < profileMass jointProfile)
    (coarse : T → C) (targetUpper conditionalUpper : ℝ)
    (htarget :
      ((normalizedProfileProbability jointProfile hmass).pushforward Prod.snd).entropyBits ≤
        targetUpper)
    (hconditional :
      ((normalizedProfileProbability jointProfile hmass).pushforward
        (fun st ↦ (st.1, coarse st.2))).conditionalEntropyBits Prod.snd ≤
          conditionalUpper) :
    (profileMass jointProfile : ℝ) * profileEntropyNats jointProfile ≤
      (profileMass jointProfile : ℝ) *
        (Real.log 2 * (targetUpper + conditionalUpper)) := by
  let joint := normalizedProfileProbability jointProfile hmass
  have hbits :=
    ProbabilityVector.entropyBits_le_add_of_right_le_of_coarsenedConditional_le
      joint coarse targetUpper conditionalUpper htarget hconditional
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnats : joint.entropy ≤ Real.log 2 * (targetUpper + conditionalUpper) := by
    unfold ProbabilityVector.entropyBits at hbits
    simpa only [mul_comm] using (div_le_iff₀ hlogTwo).mp hbits
  have hprofile : joint.entropy = profileEntropyNats jointProfile := by
    exact normalizedProfileProbability_entropy jointProfile hmass
  rw [hprofile] at hnats
  exact mul_le_mul_of_nonneg_left hnats (Nat.cast_nonneg _)

/-- Sequence-facing actual-family bound from normalized target and coarsened-conditional entropy
ceilings in bits.

The resulting per-repetition joint exponent is
`mass(sourceProfile) * log 2 * (targetUpper + conditionalUpper)` in nats.  Both entropy premises are
quantified only over actual members of `words`; no surrounding feasible class is enlarged. -/
theorem card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coarsenedBounds
    {S : Type u} {T : Type v} {C : Type w}
    [Fintype S] [Fintype T] [Fintype C]
    [DecidableEq S] [DecidableEq T] [DecidableEq C]
    (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin (profileMass sourceProfile * k) → S)
    (words : Finset (Fin (profileMass sourceProfile * k) → T))
    (coarse : T → C) (targetUpper conditionalUpper : ℝ)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (htarget : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).pushforward
        Prod.snd).entropyBits ≤ targetUpper)
    (hconditional : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).pushforward
        (fun st ↦ (st.1, coarse st.2))).conditionalEntropyBits Prod.snd ≤
          conditionalUpper) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss T sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          ((profileMass sourceProfile : ℝ) * Real.log 2 *
            (targetUpper + conditionalUpper)) ^ k := by
  apply card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow
    sourceProfile k source words
      ((profileMass sourceProfile : ℝ) * Real.log 2 *
        (targetUpper + conditionalUpper)) hmass hk hsource
  intro target htargetMem
  let jointProfile := multiplicity (jointWord source target)
  have hjointMass : profileMass jointProfile = profileMass sourceProfile * k := by
    simpa only [jointProfile, profileMass] using
      (sum_multiplicity (jointWord source target))
  have hjointMassPos : 0 < profileMass jointProfile := by
    rw [hjointMass]
    exact Nat.mul_pos hmass hk
  have htarget' :
      ((normalizedProfileProbability jointProfile hjointMassPos).pushforward
        Prod.snd).entropyBits ≤ targetUpper := by
    simpa only [jointProfile, normalizedJointWordProbability] using
      htarget target htargetMem
  have hconditional' :
      ((normalizedProfileProbability jointProfile hjointMassPos).pushforward
        (fun st ↦ (st.1, coarse st.2))).conditionalEntropyBits Prod.snd ≤
          conditionalUpper := by
    simpa only [jointProfile, normalizedJointWordProbability] using
      hconditional target htargetMem
  have hbound :=
    profileMass_mul_profileEntropyNats_le_logTwo_mul_add_of_coarsenedBounds
      jointProfile hjointMassPos coarse targetUpper conditionalUpper htarget' hconditional'
  calc
    (profileMass (multiplicity (jointWord source target)) : ℝ) *
        profileEntropyNats (multiplicity (jointWord source target)) =
      (profileMass jointProfile : ℝ) * profileEntropyNats jointProfile := rfl
    _ ≤ (profileMass jointProfile : ℝ) *
        (Real.log 2 * (targetUpper + conditionalUpper)) := hbound
    _ = (k : ℝ) *
        ((profileMass sourceProfile : ℝ) * Real.log 2 *
          (targetUpper + conditionalUpper)) := by
      rw [hjointMass, Nat.cast_mul]
      ring

/-- Equality-transported form of
`card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coarsenedBounds`.

Concrete constructions often expose a word of a syntactic length such as `N + N` together with a
proof that this equals `profileMass sourceProfile * k`.  Keeping that equality explicit avoids
client-specific casts; after substituting the length, the underlying theorem applies verbatim. -/
theorem card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coarsenedBounds_of_length_eq
    {S : Type u} {T : Type v} {C : Type w}
    [Fintype S] [Fintype T] [Fintype C]
    [DecidableEq S] [DecidableEq T] [DecidableEq C]
    {length : ℕ} (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin length → S) (words : Finset (Fin length → T))
    (coarse : T → C) (targetUpper conditionalUpper : ℝ)
    (hlength : length = profileMass sourceProfile * k)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (htarget : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (by
        simpa only [hlength] using (Nat.mul_pos hmass hk))).pushforward
          Prod.snd).entropyBits ≤ targetUpper)
    (hconditional : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (by
        simpa only [hlength] using (Nat.mul_pos hmass hk))).pushforward
        (fun st ↦ (st.1, coarse st.2))).conditionalEntropyBits Prod.snd ≤
          conditionalUpper) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss T sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          ((profileMass sourceProfile : ℝ) * Real.log 2 *
            (targetUpper + conditionalUpper)) ^ k := by
  subst length
  exact card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coarsenedBounds
    sourceProfile k source words coarse targetUpper conditionalUpper hmass hk hsource
      htarget hconditional

end AlgebraicComplexity.WordType
