/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SupportedAddressWholeStage

set_option autoImplicit false

/-! Focused trust audit for the one-copy whole stage at a single supported address. -/

#assert_axioms AlgebraicComplexity.Tensor.Restricts.supportedAddress_oneCopyWholeStage
