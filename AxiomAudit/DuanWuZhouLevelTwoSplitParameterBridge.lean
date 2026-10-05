/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSplitParameterBridge

/-! # Axiom audit for the `(1,1,2)` split-parameter bridge

The named identification of the Coppersmith--Winograd `(1,1,2)` chain's split parameter
`cw112Mu dwz112L dwz112G` with the `[duan2023faster]` section 6.3 constant `dwz63B`, and its
complementary form.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_cw112Mu_eq_dwz63B
#assert_axioms AlgebraicComplexity.Examples.dwz63_one_sub_two_cw112Mu_eq
