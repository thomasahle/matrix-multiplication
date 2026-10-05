/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellTwoTwoZeroParity

/-! # Axiom audit for the parity of a degree-two fine cell's one-slice exponent

The missing degree-two row of the middle-count table, the letterwise coarse degree of a kept
address, the letterwise `0`-or-`2` count on the counted leg, the divisibility, evenness and upper
bound of `dwz63CellOnes`, the two halved forms the zero-coordinate merge consumes, and their three
`(2,2,0)` instances.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `[duan2023faster]`, `global_value.tex` section 6.3.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwWordMiddleCount_eq_zero_or_two_of_degree_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellPower_letter_squareBlockDegree
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellPower_wordMiddleCount_eq_zero_or_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_two_dvd_cellOnes_of_target_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_even_cellOnes_of_target_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_le_of_target_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_two_mul_cellOnes_div_two_of_target_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_div_two_mem_range_of_target_two
#assert_axioms AlgebraicComplexity.Examples.dwz63_even_cellOnes_twoTwoZero
#assert_axioms AlgebraicComplexity.Examples.dwz63_cellOnes_twoTwoZero_div_two_mem_range
#assert_axioms AlgebraicComplexity.Examples.dwz63_two_mul_cellOnes_twoTwoZero_div_two
