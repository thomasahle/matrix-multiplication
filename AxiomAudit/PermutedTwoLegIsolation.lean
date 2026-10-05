/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PermutedTwoLegIsolation
import AxiomAudit.Command

/-! # Axiom audit for two-leg isolation under leg permutations -/

#assert_axioms AlgebraicComplexity.permutedAddressFamily
#assert_axioms AlgebraicComplexity.card_permutedAddressFamily
#assert_axioms AlgebraicComplexity.injOn_leg_permutedAddressFamily
#assert_axioms AlgebraicComplexity.yz_injectiveOn_cycle_permutedAddressFamily_of_xy
