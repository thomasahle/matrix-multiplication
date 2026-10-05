/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorCount

set_option autoImplicit false

/-! # Axiom audit -/

#assert_axioms AlgebraicComplexity.Examples.card_matchableCompatible_le_of_mul
#assert_axioms AlgebraicComplexity.Examples.dwz63SplitCompatTyped
#assert_axioms AlgebraicComplexity.Examples.card_dwz63FineCompetitorsTyped_le_card_matchableCompatible
#assert_axioms AlgebraicComplexity.Examples.dwz63_hcompetitorsTyped
#assert_axioms AlgebraicComplexity.Examples.dwz63_hzIndexTyped
#assert_axioms AlgebraicComplexity.Examples.dwz63_hV_of_mul
