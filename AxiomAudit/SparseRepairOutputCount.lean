/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SparseRepairOutputCount

/-! Enforcing audit for the fixed-type integral sparse-repair quotient. -/

#assert_axioms AlgebraicComplexity.two_mul_fixedTypeRepairOutputCount_mul_budget_le_fixed
#assert_axioms AlgebraicComplexity.fixedTypeRepairOutputCount_mul_budget_le_sparse_of_half
#assert_axioms
  AlgebraicComplexity.total_lt_two_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount_add_one
#assert_axioms AlgebraicComplexity.fixedTypeRepairOutputCount_pos_of_total_fits
#assert_axioms
  AlgebraicComplexity.total_le_four_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount
