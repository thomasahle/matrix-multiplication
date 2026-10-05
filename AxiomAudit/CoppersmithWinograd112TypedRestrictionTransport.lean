/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedRestrictionTransport

/-! # Axiom audit for the word-type transport along the `112` block dictionary

The vanishing of the `(1,1,2)` `alphatilde` row off the cell, the collapse of the dictionary fibre
sum and the injectivity of the pushforward it yields, the two-way word-type transport, and the
one-segment reading of a segmented restriction.

These formalize the transport needed at `[duan2023faster]`
`papers/sources/2210.10173/second_power_appendix.tex:26-45`, line `:37` (the marginal zeroing-out
inside `T_{1,1,2}^{⊗m}[α̃_Z]`), with the split `eq:tilde_A` of `second_power.tex:142-158` at the
level-two parameters of `global_value.tex:341-348`; the value being optimised is
`[coppersmith1990matrix]`, pp. 270--272. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_orbitRow_zero
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeSix_eq_zero_of_not_cell
#assert_axioms AlgebraicComplexity.Examples.dwz63_proportionalCountsSix_eq_zero_of_not_cell
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_mappedType_apply
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_mappedType_dict
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_mappedType_injOn
#assert_axioms AlgebraicComplexity.Examples.cw112_multiplicity_eq_zero_of_not_cell
#assert_axioms AlgebraicComplexity.Examples.cw112_multiplicity_positiveWordMap_Z
#assert_axioms AlgebraicComplexity.Examples.cw112_multiplicity_apply_dict
#assert_axioms AlgebraicComplexity.Examples.dwz63_keeps_constSeg_iff
#assert_axioms AlgebraicComplexity.Examples.dwz63_keeps_constSeg_of_ne
