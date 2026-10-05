/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ConditionalWordFamilyCoarsenedEntropy
import AlgebraicComplexity.Probability.MaximumEntropyDual

set_option autoImplicit false

/-!
# Coordinate-dual bounds for coarsened empirical word families

An actual finite competitor family can expose two exact probability laws for every member:

* the target law has three fixed coordinate marginals; and
* the coarsened `(source, target)` law is a fixed evaluator law.

This module turns those equalities into the target-entropy and conditional-entropy ceilings used
by `ConditionalWordFamilyCoarsenedEntropy`.  The target ceiling is certified by arbitrary
three-coordinate Gibbs potentials.  The conditional ceiling is the evaluator law's own
conditional entropy.  Consequently a concrete client only has to prove exact finite pushforward
identities and one final scalar comparison with its desired exponential base.

No tensor, compatibility relation, recursive construction, numerical certificate, or generated
datum occurs here.
-/

namespace AlgebraicComplexity

open scoped BigOperators

namespace ProbabilityVector

universe u v w x

/-- Three exact coordinate pushforwards let a probability vector use the coordinate-dual value
computed at any reference probability vector with those same marginals. -/
theorem entropyBits_le_coordinateDual_of_pushforward_eq
    {T : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    [Fintype T] [Nonempty T] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (target reference : ProbabilityVector T)
    (coordX : T → X) (coordY : T → Y) (coordZ : T → Z)
    (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (hX : target.pushforward coordX = reference.pushforward coordX)
    (hY : target.pushforward coordY = reference.pushforward coordY)
    (hZ : target.pushforward coordZ = reference.pushforward coordZ) :
    target.entropyBits ≤
      MaximumEntropyDual.coordinateDualBits
        coordX coordY coordZ reference.weight uX uY uZ := by
  have sameMarginals : MaximumEntropyDual.SameMarginals
      coordX coordY coordZ target.weight reference.weight := by
    refine ⟨?_, ?_, ?_⟩
    · funext x
      have hx := congrArg (fun p : ProbabilityVector X ↦ p.weight x) hX
      simpa only [MaximumEntropyDual.marginal, pushforward_weight] using hx
    · funext y
      have hy := congrArg (fun p : ProbabilityVector Y ↦ p.weight y) hY
      simpa only [MaximumEntropyDual.marginal, pushforward_weight] using hy
    · funext z
      have hz := congrArg (fun p : ProbabilityVector Z ↦ p.weight z) hZ
      simpa only [MaximumEntropyDual.marginal, pushforward_weight] using hz
  have hdual := MaximumEntropyDual.entropyBits_le_coordinateDual
    coordX coordY coordZ target.weight uX uY uZ target.nonneg target.total
  change target.entropyBits ≤
    MaximumEntropyDual.coordinateDualBits
      coordX coordY coordZ target.weight uX uY uZ at hdual
  exact hdual.trans_eq
    (MaximumEntropyDual.coordinateDualBits_eq_of_sameMarginals
      coordX coordY coordZ target.weight reference.weight uX uY uZ sameMarginals)

end ProbabilityVector

namespace WordType

universe u v w x y z

/-- Count an actual word family from three fixed target marginals and one fixed coarsened
evaluator law.

The word length is allowed to be presented syntactically and related to the proportional source
profile by `hlength`.  For every actual target, the three `hX`/`hY`/`hZ` hypotheses identify the
target law's coordinate pushforwards with those of `reference`, while `hcoarsened` identifies the
coarsened joint law with `evaluator`. -/
theorem card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coordinateDual
    {S : Type u} {T : Type v} {C : Type w}
    {X : Type x} {Y : Type y} {Z : Type z}
    [Fintype S] [Fintype T] [Nonempty T] [Fintype C]
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq S] [DecidableEq T] [DecidableEq C]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {length : ℕ} (sourceProfile : S → ℕ) (k : ℕ)
    (source : Fin length → S) (words : Finset (Fin length → T))
    (coarse : T → C)
    (coordX : T → X) (coordY : T → Y) (coordZ : T → Z)
    (reference : ProbabilityVector T)
    (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (evaluator : ProbabilityVector (S × C))
    (hlength : length = profileMass sourceProfile * k)
    (hmass : 0 < profileMass sourceProfile) (hk : 0 < k)
    (hsource : multiplicity source = proportionalCounts sourceProfile k)
    (hX : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (by
        simpa only [hlength] using (Nat.mul_pos hmass hk))).pushforward Prod.snd).pushforward
          coordX = reference.pushforward coordX)
    (hY : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (by
        simpa only [hlength] using (Nat.mul_pos hmass hk))).pushforward Prod.snd).pushforward
          coordY = reference.pushforward coordY)
    (hZ : ∀ target ∈ words,
      ((normalizedJointWordProbability source target (by
        simpa only [hlength] using (Nat.mul_pos hmass hk))).pushforward Prod.snd).pushforward
          coordZ = reference.pushforward coordZ)
    (hcoarsened : ∀ target ∈ words,
      (normalizedJointWordProbability source target (by
        simpa only [hlength] using (Nat.mul_pos hmass hk))).pushforward
          (fun st ↦ (st.1, coarse st.2)) = evaluator) :
    (words.card : ℝ) ≤
      conditionalFeatureEntropyLoss T sourceProfile k *
        conditionalFeatureEntropyPenaltyBase sourceProfile
          ((profileMass sourceProfile : ℝ) * Real.log 2 *
            (MaximumEntropyDual.coordinateDualBits
                coordX coordY coordZ reference.weight uX uY uZ +
              evaluator.conditionalEntropyBits Prod.snd)) ^ k := by
  subst length
  apply card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow_of_coarsenedBounds
    sourceProfile k source words coarse
      (MaximumEntropyDual.coordinateDualBits
        coordX coordY coordZ reference.weight uX uY uZ)
      (evaluator.conditionalEntropyBits Prod.snd) hmass hk hsource
  · intro target htarget
    exact ProbabilityVector.entropyBits_le_coordinateDual_of_pushforward_eq
      ((normalizedJointWordProbability source target (Nat.mul_pos hmass hk)).pushforward Prod.snd)
      reference coordX coordY coordZ uX uY uZ
      (hX target htarget) (hY target htarget) (hZ target htarget)
  · intro target htarget
    rw [hcoarsened target htarget]

end WordType
end AlgebraicComplexity
