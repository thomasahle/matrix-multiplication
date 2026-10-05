/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineConfigurationWitness
import AxiomAudit.Command

/-! # Axiom audit for the DWZ level-two fine-configuration witness -/

#assert_axioms AlgebraicComplexity.Examples.dwz63FineCountTable_symm
#assert_axioms AlgebraicComplexity.Examples.dwz63FineCountWitness_pos
#assert_axioms AlgebraicComplexity.Examples.dwz63Cell_dwz63CellIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63FineComponent_eq_dwz63CellIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63FineZLeftCount_eq_cellIndex
#assert_axioms AlgebraicComplexity.Examples.dwz63FineConfiguration_dwz63FineCountWitness
#assert_axioms AlgebraicComplexity.Examples.exists_dwz63FineConfiguration
