/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.FiniteCoreDefs
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for core finite-probability definitions

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open AlgebraicComplexity

#assert_axioms ProbabilityVector
#assert_axioms ProbabilityVector.pushforward
#assert_axioms ProbabilityVector.pushforward_weight
#assert_axioms ProbabilityVector.joint
#assert_axioms ProbabilityVector.ext
#assert_axioms ProbabilityVector.pointMass
