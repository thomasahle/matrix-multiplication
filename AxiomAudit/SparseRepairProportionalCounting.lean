/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SparseRepairProportionalCounting
import AxiomAudit.Command

/-! Enforcing axiom audit for modeled proportional sparse-family counting. -/

open AlgebraicComplexity.HoleRepair

#assert_axioms ModeledFiberFamily.card_total_le_two_mul_typeLoss_mul_sparseIndices
#assert_axioms ModeledFiberFamily.fixedTypeRepairOutputCount_mul_repairBudget_le_sparseIndices
