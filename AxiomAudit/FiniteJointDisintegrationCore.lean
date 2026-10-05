/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.FiniteJointDisintegrationCore
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for zero-safe finite joint disintegration core

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open AlgebraicComplexity

#assert_axioms ProbabilityVector.sum_snd_weight_eq_pushforward_fst_weight
#assert_axioms ProbabilityVector.conditionalSnd
#assert_axioms ProbabilityVector.conditionalSnd_weight_of_ne
#assert_axioms ProbabilityVector.weight_eq_zero_of_pushforward_fst_weight_eq_zero
#assert_axioms ProbabilityVector.pushforward_fst_weight_mul_conditionalSnd_weight
#assert_axioms ProbabilityVector.pushforward_fst_joint_conditionalSnd
