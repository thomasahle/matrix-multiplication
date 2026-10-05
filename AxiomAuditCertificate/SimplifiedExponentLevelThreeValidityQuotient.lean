/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedExponentLevelThreeValidity

/-!
# Axiom audit for quotient-parametric level-three validity adapters

These assertions cover the executable row checker and the canonical-form semantic bridge for an
arbitrary quotient slot map, together with their historical sorted-pair specializations.
-/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelThreeValidity.localRowsFor_isValid_of_mem
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelThreeValidity.branchRateOnNodesFor_eq_eval_of_canonical
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelThreeValidity.localRows_isValid_of_mem
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelThreeValidity.branchRateOnNodes_eq_eval_of_canonical
