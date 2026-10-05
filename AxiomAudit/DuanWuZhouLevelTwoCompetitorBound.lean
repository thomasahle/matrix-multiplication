/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorBound

set_option autoImplicit false

/-! # Axiom audit -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_le_ceilDiv_mul
#assert_axioms AlgebraicComplexity.Examples.dwz63_ceilDiv_le_iff
#assert_axioms AlgebraicComplexity.Examples.dwz63CompetitorBound
#assert_axioms AlgebraicComplexity.Examples.dwz63_competitorBound_spec
#assert_axioms AlgebraicComplexity.Examples.dwz63_competitorBound_le_iff
#assert_axioms AlgebraicComplexity.Examples.dwz63UniformCompetitorBound
#assert_axioms AlgebraicComplexity.Examples.dwz63_uniformCompetitorBound_spec
#assert_axioms AlgebraicComplexity.Examples.dwz63_hV_uniform
