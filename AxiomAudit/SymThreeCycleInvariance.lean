/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SymThreeCycleInvariance

set_option autoImplicit false

/-! # Axiom audit for the cyclic invariance of `sym₃` -/

#assert_axioms AlgebraicComplexity.Isomorphic.external_comm_of_map
#assert_axioms AlgebraicComplexity.Isomorphic.external_rotate
#assert_axioms AlgebraicComplexity.Isomorphic.symThree_congr
#assert_axioms AlgebraicComplexity.Isomorphic.symThree_permute_cycle
#assert_axioms AlgebraicComplexity.Isomorphic.symThree_permute_cycleSymm
#assert_axioms AlgebraicComplexity.hasTauWeight_symThree_permute_cycle_iff
#assert_axioms AlgebraicComplexity.hasTauWeight_symThree_permute_cycleSymm_iff
