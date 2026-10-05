/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.PooledMarginalProfileDefs
import AlgebraicComplexity.Probability.ComplementaryOccurrenceProjection

/-!
# Exact integral profiles for complementary-product projection

This module is the denominator-free adapter from recursive complete-split tables to pooled-parent
concentration.  A joint parent table is feasible when its ordered-state marginal is the prescribed
state profile and the sum of its two labelled occurrence marginals is the exact pooled
occurrence/symbol table.  Absolute continuity, including structural-zero rows, is derived rather
than assumed.
-/

namespace AlgebraicComplexity
namespace ComplementaryOccurrenceLaw

universe u v

variable {State : Type u} [Fintype State] [DecidableEq State]
variable {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol] [Nonempty Symbol]
variable {profile : State → ℕ}

omit [DecidableEq State] [DecidableEq Symbol] [Nonempty Symbol] in
/-- Equality of the coarse integral marginal fixes the total mass of the joint table. -/
theorem profileMass_eq_of_mappedType_fst_eq
    (joint : State × (Symbol × Symbol) → ℕ)
    (hcoarse : WordType.mappedType Prod.fst joint = profile) :
    WordType.profileMass joint = WordType.profileMass profile := by
  calc
    WordType.profileMass joint =
        WordType.profileMass (WordType.mappedType Prod.fst joint) :=
      (WordType.profileMass_mappedType Prod.fst joint).symm
    _ = WordType.profileMass profile := congrArg WordType.profileMass hcoarse

/-- **Integral pooled-feasibility bridge.**

The two displayed count equalities imply every field of
`WordType.IsPooledMarginalProfile` for the normalized complementary-product model.  In
particular, zero support is a consequence of the marginals and is not an extra client premise. -/
theorem isPooledMarginalProfile_of_mappedType_eq
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State)
    (hmass : 0 < WordType.profileMass profile)
    (joint : State × (Symbol × Symbol) → ℕ)
    (hcoarse : WordType.mappedType Prod.fst joint = profile)
    (hpool : ∀ state symbol,
      WordType.mappedType
          (fun sample : State × (Symbol × Symbol) ↦ (sample.1, sample.2.1))
          joint (state, symbol) +
        WordType.mappedType
          (fun sample : State × (Symbol × Symbol) ↦
            (complement sample.1, sample.2.2))
          joint (state, symbol) =
      law.cellJointProfile complement id (state, symbol)) :
    let M := law.toComplementaryProductProjectionModel complement hmass
    WordType.IsPooledMarginalProfile
      M.toSparsePooledMarginalProjectionModel joint := by
  classical
  let M := law.toComplementaryProductProjectionModel complement hmass
  have hjointMass : WordType.profileMass joint = WordType.profileMass profile :=
    profileMass_eq_of_mappedType_fst_eq joint hcoarse
  have hjointMassPos : 0 < WordType.profileMass joint := by
    rw [hjointMass]
    exact hmass
  let q := WordType.normalizedProfileProbability joint hjointMassPos
  have hcoarseProbability :
      q.pushforward M.coarse = M.reference.pushforward M.coarse := by
    apply ProbabilityVector.ext
    funext state
    rw [WordType.normalizedProfileProbability_pushforward_weight]
    rw [M.reference_pushforward_coarse]
    change (WordType.mappedType Prod.fst joint state : ℝ) /
        WordType.profileMass joint =
      (profile state : ℝ) / WordType.profileMass profile
    rw [hcoarse, hjointMass]
  have hpoolProbability : ∀ feature,
      (q.pushforward M.leftFeature).weight feature +
          (q.pushforward M.rightFeature).weight feature =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature := by
    rintro ⟨state, symbol⟩
    rw [WordType.normalizedProfileProbability_pushforward_weight,
      WordType.normalizedProfileProbability_pushforward_weight]
    change
      (WordType.mappedType
            (fun sample : State × (Symbol × Symbol) ↦ (sample.1, sample.2.1))
            joint (state, symbol) : ℝ) /
          WordType.profileMass joint +
        (WordType.mappedType
            (fun sample : State × (Symbol × Symbol) ↦
              (complement sample.1, sample.2.2))
            joint (state, symbol) : ℝ) /
          WordType.profileMass joint = _
    rw [← add_div, ← Nat.cast_add, hpool state symbol, hjointMass]
    exact law.toComplementaryProductProjectionModel_reference_pooledFeature_weight
      complement hmass state symbol |>.symm
  have habsolutelyContinuous : q.IsAbsolutelyContinuous M.reference :=
    M.isAbsolutelyContinuous_of_coarse_eq_of_pooledFeature_eq
      q hcoarseProbability hpoolProbability
  change WordType.IsPooledMarginalProfile
    M.toSparsePooledMarginalProjectionModel joint
  refine ⟨?_, ?_, ?_⟩
  · intro sample href
    have hqzero : q.weight sample = 0 := habsolutelyContinuous sample href
    change (joint sample : ℝ) / WordType.profileMass joint = 0 at hqzero
    have hdenom : (WordType.profileMass joint : ℝ) ≠ 0 := by
      exact_mod_cast hjointMassPos.ne'
    have hcast : (joint sample : ℝ) = 0 := (div_eq_zero_iff).mp hqzero |>.resolve_right hdenom
    exact_mod_cast hcast
  · intro state
    change (WordType.mappedType M.coarse joint state : ℝ) /
        WordType.profileMass joint = _
    calc
      (WordType.mappedType M.coarse joint state : ℝ) /
          WordType.profileMass joint =
          (q.pushforward M.coarse).weight state := by
            rw [WordType.normalizedProfileProbability_pushforward_weight]
      _ = (M.reference.pushforward M.coarse).weight state := by
            rw [hcoarseProbability]
  · rintro ⟨state, symbol⟩
    change
      (WordType.mappedType M.leftFeature joint (state, symbol) : ℝ) /
          WordType.profileMass joint +
        (WordType.mappedType M.rightFeature joint (state, symbol) : ℝ) /
          WordType.profileMass joint = _
    calc
      (WordType.mappedType M.leftFeature joint (state, symbol) : ℝ) /
          WordType.profileMass joint +
        (WordType.mappedType M.rightFeature joint (state, symbol) : ℝ) /
          WordType.profileMass joint =
          (q.pushforward M.leftFeature).weight (state, symbol) +
            (q.pushforward M.rightFeature).weight (state, symbol) := by
              rw [WordType.normalizedProfileProbability_pushforward_weight,
                WordType.normalizedProfileProbability_pushforward_weight]
      _ = (M.reference.pushforward M.leftFeature).weight (state, symbol) +
          (M.reference.pushforward M.rightFeature).weight (state, symbol) :=
        hpoolProbability (state, symbol)

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
