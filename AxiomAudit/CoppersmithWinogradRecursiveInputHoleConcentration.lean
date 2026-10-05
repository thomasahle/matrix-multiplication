/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveInputHoleConcentration

/-! Focused trust audit for recursive CW input-profile concentration. -/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwRecursivePairedChildSplitWord_injective
#assert_axioms concat_cwRecursivePairedChildSplitWord
#assert_axioms cwRecursiveExactTarget_isPooledMarginalProfile
#assert_axioms cwRecursiveExactTarget_hasParentDeviation_of_not_approximatelyMatches
#assert_axioms card_cwRecursiveInputProfileHoles_le_pooledMarginalDeviatingWords
#assert_axioms card_cwRecursiveInputProfileHoles_le
