/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainUniformBatch

set_option autoImplicit false

/-! # Axiom audit for DuanWuZhouLevelTwoPlainUniformBatch -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_card_le_two_mul_mul_div
#assert_axioms AlgebraicComplexity.Examples.dwz63_hbudget_uniformBatch
#assert_axioms AlgebraicComplexity.Examples.dwz63_hbatch_uniformBatch
