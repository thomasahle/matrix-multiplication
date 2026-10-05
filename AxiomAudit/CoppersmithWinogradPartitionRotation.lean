/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradPartitionRotation

/-! # Axiom audit for the cyclic rotation of the CW partition

The two inverse address transports on the CW alphabet, the rotation-closure of the six-address
support, the two constituent identities extended by zero to every address, and the two
partition-level rotation equalities
`(cwPartitionedTensor K q).permute cycle = cwPartitionedTensor K q` and its `cycle.symm` twin.

Paper step: `[duan2023faster]` arXiv:2210.10173, `second_power.tex:142-158`
(`lem:non-rot-values`, the requirement `α(1,1,2) = α(1,2,1) = α(2,1,1)`) and `:235`
(`note:T112`): the level-two component `T_{1,1,2}` has no non-rotational value, so one
`V^{(3)}` is read on all three of its cyclic rotations; the level-two split for the two
rotated rows is the symmetric degree-one one of `global_value.tex:347`.  The proof of
`lem:non-rot-values` (d) is `second_power_appendix.tex:26-45`.  The Lean statements themselves
are reusable partitioned-tensor infrastructure, not published claims. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwBlockAddress_permute_cycle_symm
#assert_axioms AlgebraicComplexity.Examples.cwBlockAddress_permute_cycleSymm_symm
#assert_axioms AlgebraicComplexity.Examples.mem_cwBlockSupport_ofLegs_cycle
#assert_axioms AlgebraicComplexity.Examples.mem_cwBlockSupport_ofLegs_cycleSymm
#assert_axioms AlgebraicComplexity.Examples.cwConstituentOfBlocks_cycle_of_all
#assert_axioms AlgebraicComplexity.Examples.cwConstituentOfBlocks_cycleSymm_of_all
#assert_axioms AlgebraicComplexity.Examples.cwPartitionedTensor_permute_cycle
#assert_axioms AlgebraicComplexity.Examples.cwPartitionedTensor_permute_cycleSymm
