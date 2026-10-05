/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordCore
import AxiomAudit.Command

/-! Axiom audit for the complete-split word alphabet. -/

open AlgebraicComplexity

#assert_axioms splitWordWeight
