/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SymSixDistribution

set_option autoImplicit false

/-! # Axiom audit for the `sym₆` distribution laws -/

#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.symSix_congr
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.symThree_indexedDirectSum_uniform
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.symSix_indexedDirectSum_uniform
#assert_axioms AlgebraicComplexity.Tensor.HasTauWeight.symSix_indexedDirectSum_uniform
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.symThree_external
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.symSix_external
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.symSix_power_positive
#assert_axioms AlgebraicComplexity.Tensor.Isomorphic.symSix_external_power_positive
