/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.ConditionalMaximumEntropyDual

set_option autoImplicit false

/-!
# Conditional integer-weight entropy duals

Positive integer row weights turn every exponential partition in the generic conditional dual
into the logarithm of a natural-number sum.  Generated certificates may therefore choose their
weights by untrusted numerical optimization while leaving only finite integer sums and logarithms
to the kernel-checked evaluator.

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open scoped BigOperators

namespace MatrixMultiplication.ConditionalIntegerEntropyDual

open AlgebraicComplexity

noncomputable section

universe u v

/-- Natural-number partition of one conditional row. -/
def integerFiberPartition
    {Z : Type u} {U : Type v} [Fintype U]
    (weight : Z → U → ℕ) (z : Z) : ℕ :=
  ∑ u, weight z u

/-- Positive pointwise weights give a positive row partition. -/
theorem integerFiberPartition_pos
    {Z : Type u} {U : Type v} [Fintype U] [Nonempty U]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u) (z : Z) :
    0 < integerFiberPartition weight z := by
  unfold integerFiberPartition
  exact Finset.sum_pos (fun u _ ↦ hweight z u) Finset.univ_nonempty

/-- Exponentiating logarithmic integer weights turns the analytic partition into the cast of the
integer row sum. -/
theorem partition_log_integerWeight
    {Z : Type u} {U : Type v} [Fintype U]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u) (z : Z) :
    AlgebraicComplexity.MaximumEntropyDual.partition
        (fun u ↦ Real.log (weight z u : ℝ)) =
      (integerFiberPartition weight z : ℝ) := by
  unfold AlgebraicComplexity.MaximumEntropyDual.partition integerFiberPartition
  push_cast
  apply Finset.sum_congr rfl
  intro u _hu
  rw [Real.exp_log]
  exact_mod_cast hweight z u

/-- Parent-weighted logarithms of the integer row partitions, in natural-log units. -/
def integerPartitionLogNats
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z) (weight : Z → U → ℕ) : ℝ :=
  ∑ z, parent.weight z * Real.log (integerFiberPartition weight z : ℝ)

/-- Expected logarithmic integer weight of a finite channel, in natural-log units. -/
def integerWeightExpectationNats
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (weight : Z → U → ℕ) : ℝ :=
  ∑ z, parent.weight z *
    ∑ u, (row z).weight u * Real.log (weight z u : ℝ)

/-- The integer-weight conditional dual in natural-log units. -/
def conditionalIntegerDualNats
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (weight : Z → U → ℕ) : ℝ :=
  integerPartitionLogNats parent weight -
    integerWeightExpectationNats parent row weight

/-- The same integer-weight conditional dual measured in bits. -/
def conditionalIntegerDualBits
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (weight : Z → U → ℕ) : ℝ :=
  conditionalIntegerDualNats parent row weight / Real.log 2

/-- Positive integer row weights give a rigorous conditional-entropy upper bound. -/
theorem conditionalEntropy_le_conditionalIntegerDualNats
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u) :
    (parent.joint row).conditionalEntropy Prod.fst ≤
      conditionalIntegerDualNats parent row weight := by
  have hdual :=
    AlgebraicComplexity.ProbabilityVector.conditionalEntropy_joint_fst_le_sum_logPartition_sub_expectation
      parent row (fun z u ↦ Real.log (weight z u : ℝ))
  simp_rw [partition_log_integerWeight weight hweight] at hdual
  simpa only [conditionalIntegerDualNats, integerPartitionLogNats,
    integerWeightExpectationNats, mul_sub, Finset.sum_sub_distrib] using hdual

/-- Base-two form of `conditionalEntropy_le_conditionalIntegerDualNats`. -/
theorem conditionalEntropyBits_le_conditionalIntegerDualBits
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u) :
    (parent.joint row).conditionalEntropyBits Prod.fst ≤
      conditionalIntegerDualBits parent row weight := by
  unfold AlgebraicComplexity.ProbabilityVector.conditionalEntropyBits
    conditionalIntegerDualBits
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    (conditionalEntropy_le_conditionalIntegerDualNats parent row weight hweight)

/-- Fixed-moment client form: once the score expectation has been identified with certificate
data, only the weighted integer partition logarithms and that fixed moment remain. -/
theorem conditionalEntropyBits_le_integerPartitionLog_sub_fixedMoment
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (fixedMomentNats : ℝ)
    (hmoment : integerWeightExpectationNats parent row weight = fixedMomentNats) :
    (parent.joint row).conditionalEntropyBits Prod.fst ≤
      (integerPartitionLogNats parent weight - fixedMomentNats) / Real.log 2 := by
  have hdual := conditionalEntropyBits_le_conditionalIntegerDualBits
    parent row weight hweight
  simpa only [conditionalIntegerDualBits, conditionalIntegerDualNats, hmoment] using hdual

end

end MatrixMultiplication.ConditionalIntegerEntropyDual
