/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.PositiveExternalPower

/-!
# Axiom audit for positive powers of external tensor products

This focused audit checks the successor-shaped coherence theorem and its certificate-facing
positive-exponent wrapper without importing asymptotic rank, matrix multiplication, or the
`τ`-value calculus.
-/

#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.power_external_positive
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.power_external_of_pos
