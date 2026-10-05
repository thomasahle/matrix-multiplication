/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.CrossEntropyDefs

/-!
# Pooled marginal projection models: lightweight definitions

This file contains only the data and feasibility predicates for pooled occurrence projections.
The entropy, KL-data-processing, structural-support, and quadratic inequalities live in
`PooledMarginalProjection.lean`.  Keeping this boundary small lets concrete product-reference
models be defined without importing the much larger analytic theorem closure.
-/

namespace AlgebraicComplexity

universe u₁ u₂ u₃

/-- A positive finite reference law whose log-density depends on a coarse statistic and on the
pooled occurrences of two features with a common alphabet. -/
structure PooledMarginalProjectionModel
    (S : Type u₁) (U : Type u₂) (A : Type u₃)
    [Fintype S] [Fintype U] [Fintype A] where
  reference : ProbabilityVector S
  coarse : S → U
  leftFeature : S → A
  rightFeature : S → A
  coarsePotential : U → ℝ
  featurePotential : A → ℝ
  reference_pos : ∀ s, 0 < reference.weight s
  log_reference_weight : ∀ s,
    Real.log (reference.weight s) =
      coarsePotential (coarse s) +
        (featurePotential (leftFeature s) + featurePotential (rightFeature s))

namespace PooledMarginalProjectionModel

variable
    {S : Type u₁} {U : Type u₂} {A : Type u₃}
    [Fintype S] [Fintype U] [Fintype A]
    [DecidableEq U] [DecidableEq A]

/-- Feasible laws preserve the coarse marginal and the sum of the two occurrence-feature
marginals.  They need not preserve either labelled feature marginal separately. -/
def IsFeasible (M : PooledMarginalProjectionModel S U A)
    (q : ProbabilityVector S) : Prop :=
  q.pushforward M.coarse = M.reference.pushforward M.coarse ∧
    ∀ a,
      (q.pushforward M.leftFeature).weight a +
          (q.pushforward M.rightFeature).weight a =
        (M.reference.pushforward M.leftFeature).weight a +
          (M.reference.pushforward M.rightFeature).weight a

end PooledMarginalProjectionModel

/-- A sparse finite reference law with one coarse potential and a common potential for two pooled
occurrence features.  The log-density equation is required only on its positive support. -/
structure SparsePooledMarginalProjectionModel
    (S : Type u₁) (U : Type u₂) (A : Type u₃)
    [Fintype S] [Fintype U] [Fintype A] where
  reference : ProbabilityVector S
  coarse : S → U
  leftFeature : S → A
  rightFeature : S → A
  coarsePotential : U → ℝ
  featurePotential : A → ℝ
  log_reference_weight : ∀ s, 0 < reference.weight s →
    Real.log (reference.weight s) =
      coarsePotential (coarse s) +
        (featurePotential (leftFeature s) + featurePotential (rightFeature s))

namespace SparsePooledMarginalProjectionModel

variable
    {S : Type u₁} {U : Type u₂} {A : Type u₃}
    [Fintype S] [Fintype U] [Fintype A]
    [DecidableEq U] [DecidableEq A]

/-- Sparse pooled feasibility adds absolute continuity to the coarse and pooled occurrence
constraints. -/
def IsFeasible (M : SparsePooledMarginalProjectionModel S U A)
    (q : ProbabilityVector S) : Prop :=
  q.IsAbsolutelyContinuous M.reference ∧
    q.pushforward M.coarse = M.reference.pushforward M.coarse ∧
    ∀ a,
      (q.pushforward M.leftFeature).weight a +
          (q.pushforward M.rightFeature).weight a =
        (M.reference.pushforward M.leftFeature).weight a +
          (M.reference.pushforward M.rightFeature).weight a

end SparsePooledMarginalProjectionModel

end AlgebraicComplexity
