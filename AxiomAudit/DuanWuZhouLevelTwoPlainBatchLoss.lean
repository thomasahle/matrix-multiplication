/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchLoss

set_option autoImplicit false

/-! # Axiom audit for the Hole-Lemma batching factor -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_subexponential_affine
#assert_axioms AlgebraicComplexity.Examples.dwz63_subexponential_natCast_le_affine
#assert_axioms AlgebraicComplexity.Examples.dwz63_subexponential_batchLoss
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_plainLinearBatchedStageAndLeaf
