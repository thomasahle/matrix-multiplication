/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellLiveLegs

/-! # Axiom audit for the live-leg middle-count symmetry

The letterwise fact that a zero-coordinate supported Coppersmith--Winograd letter is middle on one
live leg exactly when it is middle on the other, and its word form equating the two live legs'
middle counts. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.cwSupported_middleIndicator_liveLegs_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63_middleCount_liveLegs_eq
