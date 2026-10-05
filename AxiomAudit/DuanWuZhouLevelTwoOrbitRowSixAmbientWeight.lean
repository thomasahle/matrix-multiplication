/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRowSixAmbientWeight

/-! # Axiom audit for the symmetric ambient power's `tau`-weight

Formalizes `[duan2023faster]` `second_power_appendix.tex:26-45` (count the surviving triples, each
of the same volume), resting on Coppersmith--Winograd (1990), pp. 270--272. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cw112SymmetricAmbientHasTauWeight
