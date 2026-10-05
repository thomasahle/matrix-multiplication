/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.TauValueConstantDirectSum

/-! # Axiom audit for the constant-direct-sum `tau`-weight adapter -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.HasTauWeight.ofConstantIndexedDirectSum
