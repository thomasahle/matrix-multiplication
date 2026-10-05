/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeededPeriod

set_option autoImplicit false

/-! # Axiom audit for the per-period seeded stage

`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-121, 130-140`, with `hole_lemma.tex:159-168`,
at the section 6.3 instance `global_value.tex:332-378`. -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_seededPeriod_step
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_seededPeriod
