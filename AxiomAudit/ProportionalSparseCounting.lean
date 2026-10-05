/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ProportionalSparseCounting
import AxiomAudit.Command

/-! Enforcing axiom audit for proportional sparse-family arithmetic. -/

open AlgebraicComplexity

#assert_axioms card_le_two_mul_loss_mul_sparse_of_cover
#assert_axioms two_mul_fixedTypeRepairOutputCount_mul_budget_le_fixed
#assert_axioms fixedTypeRepairOutputCount_mul_budget_le_sparse_of_half
#assert_axioms total_lt_two_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount_add_one
#assert_axioms fixedTypeRepairOutputCount_pos_of_total_fits
#assert_axioms total_le_four_mul_loss_mul_budget_mul_fixedTypeRepairOutputCount
