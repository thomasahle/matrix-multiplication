/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFinitePeriod
import AxiomAudit.Command

/-! Audit of the literal second-power integral schedule in [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_finitePeriod_schedule
