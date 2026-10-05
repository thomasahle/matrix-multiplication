/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SplitRequirementsBoundaryReflection
import AxiomAudit.Command

/-! Audit of the reflected-boundary compatibility constructor in [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms
  AlgebraicComplexity.CompatibleSplit.SplitRequirements.isCompatible_of_reflectedBoundary
