/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceSource

/-! Certificate-tier trust audit for exact level-four occurrence source realization. -/

open AlgebraicComplexity.Examples

#assert_axioms levelFourOccurrenceSourceProfile
#assert_axioms profileMass_levelFourOccurrenceSourceProfile
#assert_axioms levelFourOccurrenceParentTerm
#assert_axioms levelFourOccurrenceParentTerm_multiplicity
#assert_axioms cwRecursiveLogicalParent_levelFourOccurrenceParentTerm_refl
#assert_axioms levelFourOccurrenceTermChildShape
#assert_axioms levelFourOccurrenceTermChildShape_get
#assert_axioms levelFourOccurrenceTermChildShape_complement
#assert_axioms levelFourOccurrenceSplitType
#assert_axioms levelFourOccurrenceSplitType_count
#assert_axioms exists_levelFourOccurrenceStateWord_of_markedReference
