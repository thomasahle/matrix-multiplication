/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroTypeClassGrowth
import AxiomAudit.Command

/-! Axiom audit for entropy growth of exact zero-coordinate CW interfaces. -/

namespace AlgebraicComplexity.Examples

#assert_axioms
  two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_cwZeroInterface

end AlgebraicComplexity.Examples
