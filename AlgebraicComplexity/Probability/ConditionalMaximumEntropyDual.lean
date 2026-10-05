/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.EntropyChainRule
import AlgebraicComplexity.Probability.MaximumEntropyDual

set_option autoImplicit false

/-!
# Conditional finite maximum-entropy duals

Gibbs' inequality may be applied independently in every row of a finite channel.  This file
packages that elementary composition: an arbitrary score on each row upper-bounds the conditional
entropy of the corresponding joint law.  No coordinate decomposition, optimizer, tensor, or
matrix-multiplication datum is built into the statement.

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open scoped BigOperators

namespace AlgebraicComplexity

namespace ProbabilityVector

universe u v

/-- An arbitrary rowwise exponential-family score upper-bounds the conditional entropy of a
finite joint law.

The score is measured in natural-log units.  The right-hand side is the parent-weighted sum of
the row log-partitions minus the corresponding score expectations. -/
theorem conditionalEntropy_joint_fst_le_sum_logPartition_sub_expectation
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (score : Z → U → ℝ) :
    (parent.joint row).conditionalEntropy Prod.fst ≤
      ∑ z, parent.weight z *
        (Real.log (MaximumEntropyDual.partition (score z)) -
          ∑ u, (row z).weight u * score z u) := by
  rw [conditionalEntropy_joint_fst]
  apply Finset.sum_le_sum
  intro z _hz
  apply mul_le_mul_of_nonneg_left _ (parent.nonneg z)
  simpa only [ProbabilityVector.entropy, MaximumEntropyDual.entropy] using
    MaximumEntropyDual.entropy_le_logPartition_sub_expectation
      (row z).weight (score z) (row z).nonneg (row z).total

end ProbabilityVector

end AlgebraicComplexity
