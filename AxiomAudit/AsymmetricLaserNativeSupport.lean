/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserNativeSupport
import AxiomAudit.Command

/-! Audit of decoded native support for [duan2023faster]. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.AsymmetricLaserData.splitRequirementsFromProfiles_support
