/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTripleEntropyBound

set_option autoImplicit false

/-! # Axiom audit for the discharge of `Dwz63TripleEntropyBound`

The cell readings of the dual gap, the exact gap identity at `alpha`, and the unconditional
discharge of `Dwz63TripleEntropyBound` from weak duality plus the committed numeric certificate.
Five cells --- rows `0`, `1`, `2`, `8`, `13` --- enter with an inverted argument.

Primary source: `[duan2023faster]`.  The general fixed-marginal argument is
`lem:numtriple_singledist`, `papers/sources/2210.10173/hashing.tex:63-70`, used in the section 6.2
analysis at `papers/sources/2210.10173/global_value.tex:292-323`; the fifteen-cell numbers are the
section 6.3 level-two example, `papers/sources/2210.10173/global_value.tex:350-375` (Table 2). -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_gibbsCell
#assert_axioms AlgebraicComplexity.Examples.dwz63_gibbsCellInv
#assert_axioms AlgebraicComplexity.Examples.dwz63_gibbsScore_eq_log
#assert_axioms AlgebraicComplexity.Examples.dwz63_gibbsScore_expectation
#assert_axioms AlgebraicComplexity.Examples.dwz63GibbsCellTerm
#assert_axioms AlgebraicComplexity.Examples.dwz63_gibbsCellTerm_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_sum_gibbsCellTerm
#assert_axioms AlgebraicComplexity.Examples.dwz63_log_partitionSum
#assert_axioms AlgebraicComplexity.Examples.dwz63_logPartition_sub_alphaScore
#assert_axioms AlgebraicComplexity.Examples.dwz63_tripleEntropyBound
