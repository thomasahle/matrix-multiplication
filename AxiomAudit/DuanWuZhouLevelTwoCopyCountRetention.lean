/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCopyCountRetention

set_option autoImplicit false

/-! # Axiom audit for the retention-form copy count -/

#assert_axioms AlgebraicComplexity.Examples.dwz63_copyCount_of_retention
#assert_axioms AlgebraicComplexity.Examples.dwz63_copyCount_fintype_of_retention
