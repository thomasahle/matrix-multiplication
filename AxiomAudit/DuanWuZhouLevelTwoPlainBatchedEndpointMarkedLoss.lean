/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMarkedLoss

set_option autoImplicit false

/-! # Axiom audit for the loss-generalised endpoint and its joint-class instance

The batched endpoint at the margin with the hash loss freed to a subexponential binder, and its
instance at the joint type class, where the marked-family and hashing-branch binders are
discharged.  Both statements remain conditional on the stage, the batch count and the leaf data.

Primary source: `[duan2023faster]`, the hashing branch and modulus at
`papers/sources/2210.10173/hashing.tex:7-28` and
`papers/sources/2210.10173/global_value.tex:130-140`, at the level-two instance of section 6.3,
`papers/sources/2210.10173/global_value.tex:332-348` (Table 2 at `:354-378`). -/

#assert_axioms
  AlgebraicComplexity.Examples.omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_markedLoss
#assert_axioms
  AlgebraicComplexity.Examples.omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_joint
