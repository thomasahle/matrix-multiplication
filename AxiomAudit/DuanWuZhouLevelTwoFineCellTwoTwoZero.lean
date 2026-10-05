/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellTwoTwoZero

/-! # Axiom audit for the `(2,2,0)` fine cell

The supported coarse `(2,2,0)` block, the constant coarse word and its identification with the
cell's target, the target's membership in the coarsened power's support, the identification of the
cell's support with a coarsening preimage (the vacuity of the split constraint on the split leg),
the exact restriction onto the `(n+1)`-th power of the coarse constituent, the point-mass row
eleven of `dwz63AlphaTilde`, and the exact and `eps`-shaved weights.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`; the value
`V_tau(T_{2,2,0}) = (q^2 + 2)^tau` is `lem:non-rot-values` (c),
`papers/sources/2210.10173/second_power.tex:144-152` (line 150). -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_cwSquare220_mem_support
#assert_axioms AlgebraicComplexity.Examples.dwz63SquareTwoTwoZero
#assert_axioms AlgebraicComplexity.Examples.dwz63SquareTwoTwoZero_val
#assert_axioms AlgebraicComplexity.Examples.dwz63_supportWordBlockAddress_const_square
#assert_axioms AlgebraicComplexity.Examples.dwz63_supportWordBlockAddress_squareTwoTwoZero_eq_target
#assert_axioms AlgebraicComplexity.Examples.dwz63_zeroCellTarget_mem_coarsen_support
#assert_axioms AlgebraicComplexity.Examples.dwz63_twoTwoZeroCell_support_eq_coarseningPreimage
#assert_axioms AlgebraicComplexity.Examples.dwz63_twoTwoZeroCell_restricts_power
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTilde_eleven_apply_zeroPair
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTilde_eleven_eq_zero_of_ne
#assert_axioms AlgebraicComplexity.Examples.dwz63_proportionalCounts_alphaTilde_eleven
#assert_axioms AlgebraicComplexity.Examples.dwz63_hasTauWeight_fineCellTwoTwoZero
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_fineCellWeight_eleven
