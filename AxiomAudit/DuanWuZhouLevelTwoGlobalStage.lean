/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalStage

/-! Focused trust audit for the discharge of the [DuanWuZhou2022] level-two endpoint's rank budget
and for the reduction of its remaining hypothesis.

Three groups are audited: the generic `sym_6` border-rank calculus and its instantiation at the
`q = 6` Coppersmith--Winograd square (which discharges the first conjunct of
`DwzLevelTwoAssembledStage` outright), the two marginal method-of-types estimates, and the
reduction of the endpoint to the single count-side hypothesis `DwzLevelTwoCountingStage`.

The `omega` bounds audited here remain **conditional**, now on `DwzLevelTwoCountingStage` alone;
the audit records that they use no axiom beyond `propext`, `Classical.choice` and `Quot.sound`,
not that the bound is unconditional. -/

/-! ## The `sym_6` border-rank calculus -/

#assert_axioms AlgebraicComplexity.Examples.borderRankLE_permute_cycle_symm
#assert_axioms AlgebraicComplexity.Examples.borderRankLE_permute_swapXY
#assert_axioms AlgebraicComplexity.Examples.borderRankLE_symThree
#assert_axioms AlgebraicComplexity.Examples.borderRankLE_symSix
#assert_axioms AlgebraicComplexity.Examples.asymptoticRank_symSix_le

/-! ## The rank budget of the level-two source, discharged -/

#assert_axioms AlgebraicComplexity.Examples.dwz63Source_borderRankLE
#assert_axioms AlgebraicComplexity.Examples.dwz63_asymptoticRank_symSix_le

/-! ## The two marginal profiles and their method-of-types estimates -/

#assert_axioms AlgebraicComplexity.Examples.profileMass_dwz63AlphaX
#assert_axioms AlgebraicComplexity.Examples.profileMass_dwz63AlphaZ
#assert_axioms AlgebraicComplexity.Examples.profileEntropyNats_dwz63AlphaX
#assert_axioms AlgebraicComplexity.Examples.profileEntropyNats_dwz63AlphaZ
#assert_axioms AlgebraicComplexity.Examples.dwz63_log_xRate_lt
#assert_axioms AlgebraicComplexity.Examples.dwz63_xRate_lt_exp
#assert_axioms AlgebraicComplexity.Examples.dwz63_log_zRate_lt
#assert_axioms AlgebraicComplexity.Examples.dwz63_zRate_lt_exp
#assert_axioms AlgebraicComplexity.Examples.dwz63_xRate_pow_le_card_typeClass
#assert_axioms AlgebraicComplexity.Examples.dwz63_zRate_pow_le_card_typeClass

/-! ## The strict rate gap and the subexponential absorption -/

#assert_axioms AlgebraicComplexity.Examples.dwz63TrueCopyRate_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63TrueGlobalRate_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63_globalRate_lt_trueGlobalRate
#assert_axioms AlgebraicComplexity.Examples.dwz63_rankBudget_lt_trueGlobalRate_pow
#assert_axioms AlgebraicComplexity.Examples.exists_cutoff_pow_le_of_pow_le_subexponential_mul

/-! ## The reduction to the count side -/

#assert_axioms AlgebraicComplexity.Examples.exists_value_of_repairedStage_true
#assert_axioms AlgebraicComplexity.Examples.dwzLevelTwoAssembledStage_of_countingStage
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_countingStage
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_dwz63CountingStage
