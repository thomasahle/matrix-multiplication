/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualNormalized
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for normalized-row support of the restricted conditional dual

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDual

#assert_axioms normalizedJointProfileRows_supportedOnPositiveParent
#assert_axioms exists_legal_of_normalizedJointProfileParent_weight_pos
