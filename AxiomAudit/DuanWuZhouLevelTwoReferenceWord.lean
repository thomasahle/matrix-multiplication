/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoReferenceWord

/-! Focused trust audit for the section 6.3 reference word: a coarse word whose fifteen cells carry
the prescribed masses, which discharges the assembly's `R2` binder. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_referenceWord
