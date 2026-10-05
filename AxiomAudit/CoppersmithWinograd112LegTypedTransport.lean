/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinograd112LegTypedTransport

/-! # Axiom audit for the `112` word-type transport on an arbitrary leg

The dictionary fibre-sum collapse, the value at a cell letter and the injectivity of the
pushforward on cell-supported profiles, the vanishing of a cell word's type off the cell, the
forward type transport, and the one-segment reading of a segmented restriction --- all with the
constrained leg as a parameter.

Paper step: `[duan2023faster]` arXiv:2210.10173, `second_power.tex:142-158`
(`lem:non-rot-values`, the requirement `α(1,1,2) = α(1,2,1) = α(2,1,1)`) and `:235`
(`note:T112`): the level-two component `T_{1,1,2}` has no non-rotational value, so one
`V^{(3)}` is read on all three of its cyclic rotations; the level-two split for the two
rotated rows is the symmetric degree-one one of `global_value.tex:347`.  The proof of
`lem:non-rot-values` (d) is `second_power_appendix.tex:26-45`.  The Lean statements themselves
are reusable partitioned-tensor infrastructure, not published claims. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_mappedTypeAt_apply
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_mappedTypeAt_dict
#assert_axioms AlgebraicComplexity.Examples.cw112RawDict_mappedTypeAt_injOn
#assert_axioms AlgebraicComplexity.Examples.cw112_multiplicityAt_eq_zero_of_not_cell
#assert_axioms AlgebraicComplexity.Examples.cw112_multiplicity_positiveWordMapAt
#assert_axioms AlgebraicComplexity.Examples.dwz63_keepsAt_constSeg_iff
#assert_axioms AlgebraicComplexity.Examples.dwz63_keepsAt_constSeg_of_ne
