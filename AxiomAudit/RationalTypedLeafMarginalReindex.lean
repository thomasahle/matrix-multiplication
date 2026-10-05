/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafMarginalReindex

/-! # Axiom audit for marginal invariance under source relabelling -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.RationalTypedLeaf.marginalProfile_reindex
