/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradOrientedFiniteCellCore
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for finite tagged and oriented CW compatibility cells

This companion checks both public declarations in the finite-cell core supporting the exact
complete-split cells of [alman2025more], Claim 6.18
(`papers/sources/2404.16349/constituent.tex:404-429`).
-/

open AlgebraicComplexity.Examples

#assert_axioms CWOrientedCoarseCell
#assert_axioms cwOrientedCoarseCellToIndex
