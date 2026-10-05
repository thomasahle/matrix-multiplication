/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricSideMarginal

/-! # Axiom audit for the free-`beta` marginal on a degree-one leg

The primitive leaf's marginal on every leg, the symmetric degree-one row pushed along the
dictionary of a degree-one leg, the identity of the two stored copies of that split at
`j = 6.25·10^20 · k`, the three leg-general component readings of the symmetric leaf's marginal,
the shared body of the six branches, and the inclusion `himp` itself.

Paper step: `[duan2023faster]` arXiv:2210.10173, proof of `lem:non-rot-values` (d)
(`second_power_appendix.tex:26-45`, line `:37`), `second_power.tex:142-158` and `:235`
(`note:T112`), and `global_value.tex:341-348` --- especially `:347`, the symmetric degree-one
`Z`-marginal split the two rotated components `(1,2,1)` and `(2,1,1)` use; the value being
optimised is `[coppersmith1990matrix]`, pp. 270--272. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cw112BaseLeaf_marginalProfile
#assert_axioms AlgebraicComplexity.Examples.dwz63_pushedAlphaTildeSeven_eq
#assert_axioms AlgebraicComplexity.Examples.dwz121_marginal_side_eq_pushedAlphaTilde
#assert_axioms AlgebraicComplexity.Examples.cw112SymmetricLeaf_marginalProfile_fstFst
#assert_axioms AlgebraicComplexity.Examples.cw112SymmetricLeaf_marginalProfile_fstSnd
#assert_axioms AlgebraicComplexity.Examples.cw112SymmetricLeaf_marginalProfile_snd
#assert_axioms AlgebraicComplexity.Examples.dwz121_component_type_of_keepMarginal
#assert_axioms AlgebraicComplexity.Examples.cw112SymmetricKeepMarginal_symThreeKeepSide
