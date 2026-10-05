/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.AsymptoticRank

/-!
# Axiom audit for the one-tensor asymptotic-rank power law

This focused audit checks every stage of the power law directly from `Tensor/AsymptoticRank.lean`:
the strict-base upper estimate, passage to the limiting base, the complementary lower estimate,
and the resulting equality. No external-product or direct-sum asymptotic-rank theorem is imported.
-/

#assert_axioms AlgebraicComplexity.Tensor.le_of_forall_gt_le
#assert_axioms AlgebraicComplexity.Tensor.asymptoticRank_power_le_pow_of_lt
#assert_axioms AlgebraicComplexity.Tensor.asymptoticRank_power_le
#assert_axioms AlgebraicComplexity.Tensor.asymptoticRank_pow_le_asymptoticRank_power
#assert_axioms AlgebraicComplexity.Tensor.asymptoticRank_power_eq
