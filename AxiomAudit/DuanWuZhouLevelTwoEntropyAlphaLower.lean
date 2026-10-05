/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoEntropyAlphaLower

set_option autoImplicit false

/-! # Axiom audit for `H(α_X) < H(α)` at the section 6.3 table

`[duan2023faster]`, section 6.1 `sec:global-algo` and section 6.3 `sec:level-2-global`,
`papers/sources/2210.10173/global_value.tex:132-133, 332-375`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_atom_alpha0_ge
#assert_axioms AlgebraicComplexity.Examples.dwz63_atom_alpha1_ge
#assert_axioms AlgebraicComplexity.Examples.dwz63_atom_alpha2_ge
#assert_axioms AlgebraicComplexity.Examples.dwz63_negMulLog_ratio
#assert_axioms AlgebraicComplexity.Examples.dwz63_entropyAlpha_ge_bound
#assert_axioms AlgebraicComplexity.Examples.dwz63_one_lt_plainXBase
