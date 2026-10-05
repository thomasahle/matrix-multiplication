/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceInputHoleBound

/-!
# Axiom audit for the finite level-four occurrence input-hole bound
-/

open AlgebraicComplexity.Examples

#assert_axioms levelFourOccurrenceParentTerm_multiplicity_eq_succ
#assert_axioms card_levelFourOccurrenceInputProfileHoles_le
