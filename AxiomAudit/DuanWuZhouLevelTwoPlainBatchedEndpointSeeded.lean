/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointSeeded

/-! Focused trust audit for the batched endpoint at a seed chosen by the hypothesis. -/

set_option autoImplicit false

#assert_axioms
  AlgebraicComplexity.Examples.omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_seeded
