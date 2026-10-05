/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientedTypeClassGrowth
import AxiomAudit.Command

/-! Axiom audit for orientation-general zero-coordinate entropy growth. -/

namespace AlgebraicComplexity

#assert_axioms
  two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_orientedZeroSupport

end AlgebraicComplexity
