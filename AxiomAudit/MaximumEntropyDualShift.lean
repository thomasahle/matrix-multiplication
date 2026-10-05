/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Probability.MaximumEntropyDualShift

/-!
# Audit of entropy-dual score shifts

Checks the representation identities used by [duan2023faster], Algorithm
`alg:verify_sec_power`, Step `step:conv_prog_entr`,
`papers/sources/2210.10173/second_power.tex:536-563`.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.MaximumEntropyDual.partition_add_const
#assert_axioms AlgebraicComplexity.MaximumEntropyDual.logPartition_sub_expectation_add_const
#assert_axioms AlgebraicComplexity.MaximumEntropyDual.coordinateDualBits_div_log_two
