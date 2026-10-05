/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrencePairedWordCore
import AlgebraicComplexity.Combinatorics.PooledMarginalProfileDefs
import AlgebraicComplexity.Probability.ComplementaryProductProjectionMarginals
import AlgebraicComplexity.Probability.IntegralProfileProbabilityCore

/-!
# Integral profiles for complementary-product projections

This module removes an artificial identity-cell restriction from the finite pooled-occurrence
interface.  A complementary-product reference may quotient ordered states through an arbitrary
finite cell map.  If an integral fine profile has the reference coarse marginal and the sum of
its two labelled occurrence marginals, normalization is feasible for the sparse information
projection.  Structural-zero support is derived from those equalities; it is not an additional
client hypothesis.

The result is deliberately stated with literal normalized count equalities.  Concrete recursive
tensor clients can therefore discharge it by finite pushforward calculations without importing
entropy or accepting an assembled counting conclusion as a premise.
-/

namespace AlgebraicComplexity
namespace ComplementaryProductProjectionModel

universe u v w

variable {State : Type u} {Cell : Type v} {Symbol : Type w}
variable [Fintype State] [Fintype Cell] [Fintype Symbol]
variable [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]

omit [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol] in
/-- Pairing two labelled child words and then observing their arbitrary state cells recovers the
literal multiplicity of the concatenated cell/symbol occurrence word.  The two halves remain
separately labelled at fixed points of `complement`. -/
theorem pooledMappedType_parentPairWord_eq_labelledCellWord
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (state : Fin n → State) (left right : Fin n → Symbol)
    (feature : Cell × Symbol) :
    WordType.mappedType M.leftFeature
          (WordType.multiplicity
            (ComplementaryOccurrenceLaw.parentPairWord state left right)) feature +
        WordType.mappedType M.rightFeature
          (WordType.multiplicity
            (ComplementaryOccurrenceLaw.parentPairWord state left right)) feature =
      WordType.multiplicity
        (Fin.append
          (fun i ↦ (M.cellOf (state i), left i))
          (fun i ↦ (M.cellOf (M.complement (state i)), right i))) feature := by
  have hleft :
      WordType.mappedType M.leftFeature
          (WordType.multiplicity
            (ComplementaryOccurrenceLaw.parentPairWord state left right)) =
        WordType.multiplicity (fun i ↦ (M.cellOf (state i), left i)) := by
    rw [← WordType.multiplicity_comp_eq_mappedType]
    rfl
  have hright :
      WordType.mappedType M.rightFeature
          (WordType.multiplicity
            (ComplementaryOccurrenceLaw.parentPairWord state left right)) =
        WordType.multiplicity
          (fun i ↦ (M.cellOf (M.complement (state i)), right i)) := by
    rw [← WordType.multiplicity_comp_eq_mappedType]
    rfl
  rw [hleft, hright]
  exact congrFun
    (WordType.multiplicity_append
      (fun i ↦ (M.cellOf (state i), left i))
      (fun i ↦ (M.cellOf (M.complement (state i)), right i))).symm feature

/-- Literal normalized coarse and pooled occurrence counts instantiate the integral profile
predicate for an arbitrary complementary-product reference.

The support clause follows from the reference model's absolute-continuity theorem, so callers do
not have to reproduce structural-zero reasoning. -/
theorem isPooledMarginalProfile_of_normalized_marginals
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (profile : State × (Symbol × Symbol) → ℕ)
    (hmass : 0 < WordType.profileMass profile)
    (hcoarse : ∀ state,
      (WordType.mappedType M.coarse profile state : ℝ) /
          WordType.profileMass profile =
        M.stateLaw.weight state)
    (hpool : ∀ feature,
      (WordType.mappedType M.leftFeature profile feature : ℝ) /
            WordType.profileMass profile +
          (WordType.mappedType M.rightFeature profile feature : ℝ) /
            WordType.profileMass profile =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature) :
    WordType.IsPooledMarginalProfile
      M.toSparsePooledMarginalProjectionModel profile := by
  classical
  let q := WordType.normalizedProfileProbability profile hmass
  have hcoarseProbability :
      q.pushforward M.coarse = M.reference.pushforward M.coarse := by
    rw [M.reference_pushforward_coarse]
    apply ProbabilityVector.ext
    funext state
    rw [WordType.normalizedProfileProbability_pushforward_weight]
    exact hcoarse state
  have hpoolProbability : ∀ feature,
      (q.pushforward M.leftFeature).weight feature +
          (q.pushforward M.rightFeature).weight feature =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature := by
    intro feature
    rw [WordType.normalizedProfileProbability_pushforward_weight,
      WordType.normalizedProfileProbability_pushforward_weight]
    exact hpool feature
  have habsolutelyContinuous : q.IsAbsolutelyContinuous M.reference :=
    M.isAbsolutelyContinuous_of_coarse_eq_of_pooledFeature_eq
      q hcoarseProbability hpoolProbability
  refine ⟨?_, ?_, ?_⟩
  · intro sample href
    have hqzero : q.weight sample = 0 := habsolutelyContinuous sample href
    change (profile sample : ℝ) / WordType.profileMass profile = 0 at hqzero
    have hdenom : (WordType.profileMass profile : ℝ) ≠ 0 := by
      exact_mod_cast hmass.ne'
    have hcast : (profile sample : ℝ) = 0 :=
      (div_eq_zero_iff).mp hqzero |>.resolve_right hdenom
    exact_mod_cast hcast
  · intro state
    change (WordType.mappedType M.coarse profile state : ℝ) /
        WordType.profileMass profile =
      (M.reference.pushforward M.coarse).weight state
    rw [M.reference_pushforward_coarse]
    exact hcoarse state
  · intro feature
    change
      (WordType.mappedType M.leftFeature profile feature : ℝ) /
            WordType.profileMass profile +
          (WordType.mappedType M.rightFeature profile feature : ℝ) /
            WordType.profileMass profile =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature
    exact hpool feature

end ComplementaryProductProjectionModel
end AlgebraicComplexity
