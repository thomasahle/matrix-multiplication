/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112LegTypedCut

/-! # Axiom audit for the rotated orbit region's typed cut

The vanishing of the symmetric degree-one row off the cell of a degree-one leg, the pushed
profile, the typed cut on an arbitrary leg and its decidability instance, the two cut-support
characterisations, the bijection of the two cut supports, and the restriction of the rotated orbit
region onto the typed cut.

Paper step: `[duan2023faster]` arXiv:2210.10173, proof of `lem:non-rot-values` (d)
(`second_power_appendix.tex:26-45`, line `:37`), `second_power.tex:142-158` and `:235`
(`note:T112`), and `global_value.tex:341-348` --- especially `:347`, the symmetric degree-one
`Z`-marginal split the two rotated components `(1,2,1)` and `(2,1,1)` use; the value being
optimised is `[coppersmith1990matrix]`, pp. 270--272. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwSquare112_side
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeSeven_eq_zero_of_not_cell
#assert_axioms AlgebraicComplexity.Examples.dwz63_proportionalCountsSeven_eq_zero_of_not_cell
#assert_axioms AlgebraicComplexity.Examples.cw112LegPushedProfile
#assert_axioms AlgebraicComplexity.Examples.cw112LegTypedCut
#assert_axioms AlgebraicComplexity.Examples.cw112LegTypedCutKeepDecidable
#assert_axioms AlgebraicComplexity.Examples.dwz63_mem_sideOrbitRegion_support_iff
#assert_axioms AlgebraicComplexity.Examples.cw112_mem_legTypedCut_support_iff
#assert_axioms AlgebraicComplexity.Examples.cw112LegTypedCut_support_eq_image
#assert_axioms AlgebraicComplexity.Examples.dwz63_sideOrbitRegion_restricts_legTypedCut
