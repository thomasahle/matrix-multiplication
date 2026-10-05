/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricMarginalCut

/-! # Axiom audit for the three-marginal cut of the `112` value certificate

The `Z` marginal of the `(L,L,G,G)` leaf, the pushed `alphatilde` row, the identity of the two
stored copies of the `b`-split at `j = 4·10^13 · k`, the letterwise readings of the label
transpose, and the `Z` component of the certificate's leg marginal.  Formalizes
`[DuanWuZhou2022]` `second_power_appendix.tex:47`, `second_power.tex:174-181` (`def:complv2`) and
`global_value.tex:341-348`. -/

set_option autoImplicit false

open AlgebraicComplexity.Examples

#assert_axioms cw112BaseLeaf_marginalProfile_Z
#assert_axioms dwz63_pushedAlphaTildeSix_eq
#assert_axioms dwz112_marginal_projZ_eq_pushedAlphaTilde
#assert_axioms dwz63_positiveWordEquiv_symThreeWordEquiv
#assert_axioms dwz63_positiveWordEquiv_symThreeWordEquiv_symm
#assert_axioms cw112SymmetricLeaf_marginalProfile_projZ
