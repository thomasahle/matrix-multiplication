/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitBetaCanonical

/-! # Axiom audit for rows 7 and 10, hypothesis-free

Rows `7` and `10` of the fine leaf's orbit premise, at `eps = dwz63LeafMargin`, with no
hypothesis beyond the assembly's own lattice and cutoff conditions.

Paper step: `[duan2023faster]` arXiv:2210.10173, proof of `lem:non-rot-values` (d)
(`second_power_appendix.tex:26-45`, line `:37`), `second_power.tex:142-158` and `:235`
(`note:T112`), and `global_value.tex:341-348` --- especially `:347`, the symmetric degree-one
`Z`-marginal split the two rotated components `(1,2,1)` and `(2,1,1)` use; the value being
optimised is `[coppersmith1990matrix]`, pp. 270--272. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_orbitRowsSevenTen_R3
