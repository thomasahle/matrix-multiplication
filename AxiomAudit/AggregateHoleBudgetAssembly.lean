/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.AggregateHoleBudgetAssembly

set_option autoImplicit false

/-! # Axiom audit for the assembled second retention pass -/

#assert_axioms AlgebraicComplexity.AsymmetricGlobal.holeBudget_goodBatch_fiber
#assert_axioms AlgebraicComplexity.goodBatch_surjective_of_aggregateHoleFraction
#assert_axioms
  AlgebraicComplexity.AsymmetricGlobal.holeBudget_goodBatch_fiber_of_aggregateHoleFraction
