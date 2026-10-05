/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLocalizedStage

set_option autoImplicit false

/-! # Axiom audit for the localized section 6.3 stage -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_constituent_restricts_brokenReferenceLeaf
#assert_axioms AlgebraicComplexity.Examples.dwz63_plainJointRetained_mem_positivePowerSupport
#assert_axioms AlgebraicComplexity.Examples.dwz63_localizedGroupedStage_of_segmentedRepair
#assert_axioms AlgebraicComplexity.Examples.dwz63_localizedGroupedSymSixStage_of_segmentedRepair
