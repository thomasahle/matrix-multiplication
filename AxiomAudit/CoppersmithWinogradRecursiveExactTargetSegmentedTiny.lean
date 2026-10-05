/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveExactTargetSegmentedTiny

set_option autoImplicit false

/-!
# Axiom audit for the two-cell recursive exact-target client

This exact audit covers the permanent nonvacuity regression for the segmented exact-target
interface used in Claim 6.18 of [alman2025more],
`papers/sources/2404.16349/constituent.tex:376-440`.  The audited theorem constructs all target
data and exposes two distinct occupied Boolean cells; it assumes no tensor restriction, counting
bound, asymptotic estimate, or generated certificate.
-/

#assert_axioms
  AlgebraicComplexity.Examples.cwRecursiveExactTargetSegmented_twoCell_nonvacuous
