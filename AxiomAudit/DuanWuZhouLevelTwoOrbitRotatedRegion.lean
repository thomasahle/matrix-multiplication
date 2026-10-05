/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRotatedRegion

/-! # Axiom audit for the rotated orbit regions of the fine leaf

Cut-predicate congruence for partitioned certificates, the two one-leg segmented keep readings,
the `(1,1,2)`-target region cut on an arbitrary leg, the two coarse-target rotations, and the four
results identifying the `(1,2,1)` and `(2,1,1)` orbit regions --- and their `sym_3` --- with the
`X`- and `Y`-cut `(1,1,2)` region.

Paper step: `[duan2023faster]` arXiv:2210.10173, `second_power.tex:142-158`
(`lem:non-rot-values`, the requirement `α(1,1,2) = α(1,2,1) = α(2,1,1)`) and `:235`
(`note:T112`): the level-two component `T_{1,1,2}` has no non-rotational value, so one
`V^{(3)}` is read on all three of its cyclic rotations; the level-two split for the two
rotated rows is the symmetric degree-one one of `global_value.tex:347`.  The proof of
`lem:non-rot-values` (d) is `second_power_appendix.tex:26-45`.  The Lean statements themselves
are reusable partitioned-tensor infrastructure, not published claims. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.PartitionedTensor.select_congr
#assert_axioms AlgebraicComplexity.Examples.dwz63_keeps_ofLeg_self
#assert_axioms AlgebraicComplexity.Examples.dwz63_keeps_ofLeg_ne
#assert_axioms AlgebraicComplexity.Examples.dwz63SideOrbitRegion
#assert_axioms AlgebraicComplexity.Examples.dwz63AlphaTilde_ten_eq_seven
#assert_axioms AlgebraicComplexity.Examples.dwz63OrbitTarget_one_cycle_symm
#assert_axioms AlgebraicComplexity.Examples.dwz63OrbitTarget_two_cycle
#assert_axioms AlgebraicComplexity.Examples.dwz63_isomorphic_permute_cycle_orbitRegion_one
#assert_axioms AlgebraicComplexity.Examples.dwz63_isomorphic_permute_cycleSymm_orbitRegion_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_isomorphic_symThree_orbitRegion_one
#assert_axioms AlgebraicComplexity.Examples.dwz63_isomorphic_symThree_orbitRegion_two
