/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitBetaAmbientWeight

/-! # Axiom audit for the free-`beta` symmetric ambient weight

The ambient `tau`-weight rows 7 and 10 of the fine leaf's orbit premise need.  Formalizes
`[duan2023faster]` `lem:non-rot-values` (d) (`second_power.tex:145-156`,
`second_power_appendix.tex:26-45`) at the split of `global_value.tex:347`. -/

set_option autoImplicit false

#assert_axioms
  AlgebraicComplexity.Examples.exists_eventually_cw112SymmetricAmbientHasTauWeightBeta
