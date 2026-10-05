/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFinePairSum

/-! # Axiom audit for sums over the fine-letter alphabet

The two expansion lemmas over an arbitrary `AddCommMonoid` (reusable), and the `profileMass`
reading of every `alphatilde` row of the section 6.3 table (project-specific).
`[duan2023faster]`, section 6.3 `sec:level-2-global`,
`papers/sources/2210.10173/global_value.tex:332-375`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_sum_cwBlock
#assert_axioms AlgebraicComplexity.Examples.dwz63_sum_finePair_expand
#assert_axioms AlgebraicComplexity.Examples.dwz63_profileMass_alphaTilde
#assert_axioms AlgebraicComplexity.Examples.dwz63_profileMass_alphaTilde_pos
