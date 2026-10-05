/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestrictionCut

/-! # Axiom audit for the orbit region as a restriction onto the `112` typed cut

The letter-level dictionary data packaged for positive powers, the two cut supports and their
bijection, and the restriction itself.

These formalize the inclusion asserted at `[duan2023faster]`
`papers/sources/2210.10173/second_power_appendix.tex:26-45`, line `:37`, with the `Z`-marginal
split `eq:tilde_A` of `second_power.tex:142-158` at the level-two parameters of
`global_value.tex:341-348`; the value being optimised is `[coppersmith1990matrix]`,
pp. 270--272. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cw112RawCell_dict_injOn
#assert_axioms AlgebraicComplexity.Examples.cw112RawCell_dict_support_image
#assert_axioms AlgebraicComplexity.Examples.cw112RawCell_positivePower_support_image
#assert_axioms AlgebraicComplexity.Examples.dwz63_mem_orbitRegion_support_iff
#assert_axioms AlgebraicComplexity.Examples.cw112_mem_typedCut_support_iff
#assert_axioms AlgebraicComplexity.Examples.cw112TypedCut_support_eq_image
#assert_axioms AlgebraicComplexity.Examples.dwz63_orbitRegion_restricts_typedCut
