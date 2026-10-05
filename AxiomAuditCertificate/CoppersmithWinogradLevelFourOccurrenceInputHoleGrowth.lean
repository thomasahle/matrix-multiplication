/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradLevelFourOccurrenceInputHoleGrowth

/-!
# Axiom audit for asymptotic level-four occurrence input-hole absorption
-/

open AlgebraicComplexity.Examples

#assert_axioms levelFourOccurrenceInputHoleLoss_pos
#assert_axioms levelFourOccurrenceTypeSelection_mul_structuralZeroLoss_le_inputHoleLoss
#assert_axioms levelFourOccurrenceInputHoleLoss_subexponential
#assert_axioms card_levelFourOccurrenceInputProfileHoles_le_inputHoleLoss_mul_exp
#assert_axioms eventually_budget_mul_card_levelFourOccurrenceInputProfileHoles_le_of_targetGrowth
