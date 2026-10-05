/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.ConditionalMaximumEntropyDual
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for conditional finite maximum-entropy duals

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open AlgebraicComplexity

#assert_axioms
  ProbabilityVector.conditionalEntropy_joint_fst_le_sum_logPartition_sub_expectation
