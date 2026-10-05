/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointSeededLoss

/-! Focused trust audit for the seeded batched endpoint with the hash loss freed to a binder.

Paper step: `[duan2023faster]` §6.2, the assembly of the retained count, the Hole Lemma and the
leaf value into the value bound (`papers/sources/2210.10173/global_value.tex:270-305`). -/

set_option autoImplicit false

#assert_axioms
  AlgebraicComplexity.Examples.omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_seeded_loss
