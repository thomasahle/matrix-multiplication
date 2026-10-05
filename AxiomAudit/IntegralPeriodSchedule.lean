/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralPeriodSchedule
import AxiomAudit.Command

/-! Audit of the integral-subsequence convention used by [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.WordType.exists_cofinal_integral_schedule
