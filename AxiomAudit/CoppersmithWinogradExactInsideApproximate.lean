/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradExactInsideApproximate
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for exact CW selection inside an approximate interface

This audit covers the concrete CW input-profile restriction used before an exact rational
constituent extraction.  It formalizes the selector relationship implicit in [alman2025more],
`papers/sources/2404.16349/constituent.tex:113-147,338-348`.
-/

#assert_axioms AlgebraicComplexity.Examples.cwSelectedApproximateInterfaceTerm_restricts_exact
