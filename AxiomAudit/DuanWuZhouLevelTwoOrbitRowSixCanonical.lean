/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRowSixCanonical

/-! # Axiom audit for row 6 of the fine leaf's orbit premise

The canonical ambient `tau`-weight at the published value, and row
`6` of the assembly's `R3` premise with no hypothesis.  Formalizes `[duan2023faster]`
`second_power_appendix.tex:26-45` and `global_value.tex:341-348`, resting on
Coppersmith--Winograd (1990), pp. 270--272. -/

set_option autoImplicit false

open AlgebraicComplexity.Examples

#assert_axioms exists_eventually_cw112SymmetricAmbientHasTauWeight
#assert_axioms dwz63_orbitRowSix_R3
