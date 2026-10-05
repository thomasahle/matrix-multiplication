/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.EntropyDefs

/-!
# Entropy of finite probability vectors

This module deliberately contains the entropy definitions independently of KL divergence and its
inequality proofs.  Type-counting and typed-interface clients can therefore use entropy without
loading the stronger information-theoretic layer.
-/

open scoped BigOperators

namespace AlgebraicComplexity.ProbabilityVector

universe u v

variable {I : Type u} [Fintype I]

/-- A point mass has zero Shannon entropy. -/
@[simp] theorem entropy_pointMass [DecidableEq I] (i : I) :
    (pointMass i).entropy = 0 := by
  classical
  unfold entropy
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [pointMass, hji]
  · simp

/-- A point mass has zero Shannon entropy in bits. -/
@[simp] theorem entropyBits_pointMass [DecidableEq I] (i : I) :
    (pointMass i).entropyBits = 0 := by
  simp [entropyBits]

/-- Conditional entropy of the sample after revealing a deterministic finite statistic. -/
noncomputable def conditionalEntropy
    {K : Type v} [Fintype K] [DecidableEq K]
    (p : ProbabilityVector I) (f : I → K) : ℝ :=
  p.entropy - (p.pushforward f).entropy

/-- Conditional entropy measured in bits. -/
noncomputable def conditionalEntropyBits
    {K : Type v} [Fintype K] [DecidableEq K]
    (p : ProbabilityVector I) (f : I → K) : ℝ :=
  p.conditionalEntropy f / Real.log 2

/-- Entropy is minus the expected logarithmic density, with the convention `0 log 0 = 0`. -/
theorem entropy_eq_neg_expectation_log (p : ProbabilityVector I) :
    p.entropy = -p.expectation (fun i ↦ Real.log (p.weight i)) := by
  unfold entropy expectation
  simp_rw [Real.negMulLog_eq_neg]
  rw [Finset.sum_neg_distrib]

end AlgebraicComplexity.ProbabilityVector
