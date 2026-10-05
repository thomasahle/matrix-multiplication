/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightMarkedHashExtraction
import AxiomAudit.Command

/-! # Axiom audit for cyclic marked total-weight tensor extraction -/

#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightCycleMarkedPartition
#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightCycleMarkedPartition_support
#assert_axioms AlgebraicComplexity.Examples.cwTotalWeightCycleModeledTargets_restricts_marked
#assert_axioms AlgebraicComplexity.Examples.exists_seed_many_cycle_markedXY_totalWeight_extraction
#assert_axioms
  AlgebraicComplexity.Examples.exists_seed_many_cycle_markedXY_totalWeight_extraction_of_modulus
