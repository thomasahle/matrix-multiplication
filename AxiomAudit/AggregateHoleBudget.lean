/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.AggregateHoleBudget

set_option autoImplicit false

/-! # Axiom audit for the good-subset Hole-Lemma budget and its batching -/

#assert_axioms AlgebraicComplexity.AsymmetricGlobal.holeBudget_of_goodSubset
#assert_axioms AlgebraicComplexity.AsymmetricGlobal.holeBudget_fiber_of_goodSubset
#assert_axioms AlgebraicComplexity.goodBatch
#assert_axioms AlgebraicComplexity.goodBatch_of_mem
#assert_axioms AlgebraicComplexity.goodBatch_surjective
#assert_axioms AlgebraicComplexity.le_card_goodBatch_fiber
