/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellPowerSupport

/-! # Axiom audit for the one-segment localized power's support

The membership equivalence settling that the one-segment
`segmentedLocalizedSplittingPower` is the fine power selected by "coarsens to the target" and
"has pooled `Z`-type `α`" --- propositionally, not definitionally. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_mem_cellPower_support_iff
