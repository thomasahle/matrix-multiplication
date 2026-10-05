/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityFixedTypeRepair

/-! Enforcing audit for the finite largest-fiber estimates used by CW fixed-type selection. -/

#assert_axioms
  AlgebraicComplexity.Examples.exists_mem_card_le_card_image_mul_card_filter
#assert_axioms
  AlgebraicComplexity.Examples.exists_mem_card_le_card_image_mul_card_filter_reference
#assert_axioms
  AlgebraicComplexity.Examples.exists_reference_card_le_jointTypes_mul_fixedJointType
