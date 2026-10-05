/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricMarginalCutImp

/-! # Axiom audit for the marginal inclusion

The `112` value certificate's three-marginal cut sits inside `sym₃` of the leaf's `alphatilde`
`Z`-typed cut.  Formalizes `[DuanWuZhou2022]` `second_power_appendix.tex:47` and `def:complv2`
(`second_power.tex:174-181`). -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cw112SymmetricKeepMarginal_symThreeKeep
