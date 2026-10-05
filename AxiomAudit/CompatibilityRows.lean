/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.CompatibilityRows

/-! Focused trust audit for the certificate-free compatibility-row interface. -/

#assert_axioms
  MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows.rate_congr
#assert_axioms
  MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows.rate_empty
