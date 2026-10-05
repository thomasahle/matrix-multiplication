/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitBetaWeight

/-! # Axiom audit for the rotated rows' `sym₃` weight

The two rotated rows' share of the global distribution and the period reconciliation, `sym₃` of
the rotated typed cut inside the committed symmetric ambient power, the rotated region's `sym₃`
weight at `eps = 10^(-29)`, the index-length identification, and the assembly's `R3` binder for
`o ≠ 0` from an ambient weight.

Paper step: `[duan2023faster]` arXiv:2210.10173, proof of `lem:non-rot-values` (d)
(`second_power_appendix.tex:26-45`, line `:37`), `second_power.tex:142-158` and `:235`
(`note:T112`), and `global_value.tex:341-348` --- especially `:347`, the symmetric degree-one
`Z`-marginal split the two rotated components `(1,2,1)` and `(2,1,1)` use; the value being
optimised is `[coppersmith1990matrix]`, pp. 270--272. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_orbitRowsSevenTen_alpha
#assert_axioms AlgebraicComplexity.Examples.dwz63_orbitRowsSevenTen_period
#assert_axioms AlgebraicComplexity.Examples.cw112_symThree_legTypedCut_restricts_symmetricAmbient
#assert_axioms AlgebraicComplexity.Examples.dwz63_symThree_sideRegion_weight_of_ambient
#assert_axioms AlgebraicComplexity.Examples.dwz63_sideRegion_depth
#assert_axioms AlgebraicComplexity.Examples.dwz63_orbitRowsSevenTen_R3_of_ambient
