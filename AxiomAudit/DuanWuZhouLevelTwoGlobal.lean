/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobal

/-! Focused trust audit for the [DuanWuZhou2022] section 6.3 level-two endpoint `omega <
2.374631`: the finite certificate data, the five aggregated directed obligations behind the rate
table (each resting on the forty-six atanh enclosures of
`better_bound/dwz_endpoint_prep/certificate.json`), the exact rational endpoint against the
square border-rank budget `64`, and the composition through M-DWZ6's asymmetric global value
theorem.

The `omega` bound audited here is **conditional** on the single named hypothesis
`DwzLevelTwoAssembledStage` (the counting half of section 6); the audit records that the
conditional theorem uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, not that
the bound is unconditional. -/

/-! ## The finite certificate data -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_alpha_sum
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaX_marginal_0
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaX_marginal_1
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaX_marginal_2
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaX_marginal_3
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaX_marginal_4
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaZ_marginal_0
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaZ_marginal_1
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaZ_marginal_2
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaZ_marginal_3
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaZ_marginal_4
#assert_axioms AlgebraicComplexity.Examples.dwz63_partitionSum_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_average_split_mass
#assert_axioms AlgebraicComplexity.Examples.dwz63_three_mul_tau

/-! ## The five aggregated obligations, in the direction each field is consumed -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_log_xRate_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_xRate_le_exp
#assert_axioms AlgebraicComplexity.Examples.dwz63_log_zRate_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_zRate_le_exp
#assert_axioms AlgebraicComplexity.Examples.dwz63_logCompat_le_log_compatRate
#assert_axioms AlgebraicComplexity.Examples.dwz63_exp_le_compatRate
#assert_axioms AlgebraicComplexity.Examples.dwz63_log_valRate_le
#assert_axioms AlgebraicComplexity.Examples.dwz63_valRate_le_exp
#assert_axioms AlgebraicComplexity.Examples.dwz63_gibbsDeficit_le_log_hashLossMultiplier

/-! ## The endpoint and the composition -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_branchOne_lt_branchTwo
#assert_axioms AlgebraicComplexity.Examples.dwz63_endpoint_gt_64
#assert_axioms AlgebraicComplexity.Examples.dwz63RateData_globalRate
#assert_axioms AlgebraicComplexity.Examples.dwz63_rankBudget_lt_globalRate_pow
#assert_axioms AlgebraicComplexity.Examples.dwzLevelTwoAssembledStage_of_repairedStage
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_dwzLevelTwoAssembledStage
