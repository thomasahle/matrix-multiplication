/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.TauValueSuperadditivity

/-!
# Axiom audit for the three structural laws of the CW90 `τ`-value

This focused audit covers the finite semantic engine behind tensor-product
supermultiplicativity, positive-power supermultiplicativity, and direct-sum superadditivity.  It
checks both the tensor-level Pascal/degeneration bridge and the final supremum-level laws.  The
Schönhage comparison and value-to-`omega` implications are audited separately in
`AxiomAudit/TauValueSoundness.lean`.
-/

#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.externalPrefix_power_directSum_succ
#assert_axioms AlgebraicComplexity.Tensor.PolynomialDegenerates.directSum
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.matrixMultiplication_externalProduct
#assert_axioms AlgebraicComplexity.restricts_external_matrixMultiplicationDirectSum
#assert_axioms AlgebraicComplexity.HasTauWeight.external
#assert_axioms AlgebraicComplexity.HasTauWeight.directSum
#assert_axioms AlgebraicComplexity.HasTauWeight.power_succ
#assert_axioms AlgebraicComplexity.le_tauValue_of_hasTauWeight
#assert_axioms AlgebraicComplexity.mul_tauValue_le_tauValue_external
#assert_axioms AlgebraicComplexity.tauValue_pow_le_tauValue_power
#assert_axioms AlgebraicComplexity.add_pow_le_of_multiples
#assert_axioms AlgebraicComplexity.hasTauWeight_externalPrefix_power_directSum
#assert_axioms AlgebraicComplexity.tauValue_add_le_tauValue_directSum
