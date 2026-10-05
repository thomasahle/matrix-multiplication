/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionRotationPower

/-! # Axiom audit for the CW rotation through powers and cuts

Letterwise relabelling by the identity, the rotation of the raw CW square and of each of its
positive powers as reindex equivalences along the identity relabelling, and the two client forms:
rotating a block cut of a power of the raw square rotates the cut predicate and nothing else.

Paper step: `[duan2023faster]` arXiv:2210.10173, `second_power.tex:142-158`
(`lem:non-rot-values`, the requirement `α(1,1,2) = α(1,2,1) = α(2,1,1)`) and `:235`
(`note:T112`): the level-two component `T_{1,1,2}` has no non-rotational value, so one
`V^{(3)}` is read on all three of its cyclic rotations; the level-two split for the two
rotated rows is the symmetric degree-one one of `global_value.tex:347`.  The proof of
`lem:non-rot-values` (d) is `second_power_appendix.tex:26-45`.  The Lean statements themselves
are reusable partitioned-tensor infrastructure, not published claims. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.positiveWordCongrEquiv_refl
#assert_axioms AlgebraicComplexity.Examples.cwSquareRaw_reindexEquiv_permute_cycle
#assert_axioms AlgebraicComplexity.Examples.cwSquareRaw_reindexEquiv_permute_cycleSymm
#assert_axioms AlgebraicComplexity.Examples.cwSquareRawPower_reindexEquiv_permute_cycle
#assert_axioms AlgebraicComplexity.Examples.cwSquareRawPower_reindexEquiv_permute_cycleSymm
#assert_axioms AlgebraicComplexity.Examples.isomorphic_permute_cycle_rawSquarePower_select
#assert_axioms AlgebraicComplexity.Examples.isomorphic_permute_cycleSymm_rawSquarePower_select
