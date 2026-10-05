/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedCancellation

/-! # Axiom audit for the hashing seed's modulus cancellation -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_rate_le_loss_of_seed
