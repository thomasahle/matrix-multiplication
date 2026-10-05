/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoUniformCompetitorCoarse

set_option autoImplicit false

/-! # Axiom audit for the uniform left-record competitor bound

`[duan2023faster]`, §6.2 `sec:global-value`,
`papers/sources/2210.10173/global_value.tex:35, 135, 137, 176-198` (`lemma:pcomp_g`). -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_card_matchable_eq_of_multiplicity_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_card_typicalSet_eq_of_multiplicity_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_competitorBound_eq_of_mem_matchable
#assert_axioms AlgebraicComplexity.Examples.dwz63_uniform_hV_of_mem_matchable
#assert_axioms AlgebraicComplexity.Examples.dwz63_uniform_hV_coarse
