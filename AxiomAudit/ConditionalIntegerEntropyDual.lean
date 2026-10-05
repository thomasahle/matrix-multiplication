/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.ConditionalIntegerEntropyDual
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for conditional integer-weight entropy duals

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open MatrixMultiplication.ConditionalIntegerEntropyDual

#assert_axioms integerFiberPartition
#assert_axioms integerFiberPartition_pos
#assert_axioms partition_log_integerWeight
#assert_axioms integerPartitionLogNats
#assert_axioms integerWeightExpectationNats
#assert_axioms conditionalIntegerDualNats
#assert_axioms conditionalIntegerDualBits
#assert_axioms conditionalEntropy_le_conditionalIntegerDualNats
#assert_axioms conditionalEntropyBits_le_conditionalIntegerDualBits
#assert_axioms conditionalEntropyBits_le_integerPartitionLog_sub_fixedMoment
