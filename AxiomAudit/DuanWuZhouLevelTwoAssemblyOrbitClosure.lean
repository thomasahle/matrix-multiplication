/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssemblyOrbitClosure

/-! Focused trust audit for the section 6.3 endpoint with all three orbit rows discharged: the
form carrying a general batching loss, and the form fixed to the good-batch count, each leaving
only the per-period seed binder. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_seededPeriod
#assert_axioms AlgebraicComplexity.Examples.omega_lt_2374631_of_seededPeriod_goodBatchLoss
