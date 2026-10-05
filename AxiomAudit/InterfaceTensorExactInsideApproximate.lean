/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorExactInsideApproximate
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for exact selection inside an approximate interface

This audit covers the restriction-valued form of exact rational complete-split selection inside
the approximate parent interface used by the constituent stage of [alman2025more],
`papers/sources/2404.16349/constituent.tex:113-147,338-348`.
-/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.selectEncodedApproximateInterfaceTerm_to_exact
