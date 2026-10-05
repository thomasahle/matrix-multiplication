/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationInjective

/-! Focused trust audit for lossless compatibility isolation on injective supports. -/

#assert_axioms
  AlgebraicComplexity.Tensor.compatibilityIsolatedSupport_eq_ambient_of_injOn_of_rigid
#assert_axioms
  AlgebraicComplexity.Tensor.compatibilityCompetitorIncidence_eq_zero_of_injOn_of_rigid
