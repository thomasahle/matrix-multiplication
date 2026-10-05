/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.CoppersmithWinogradZeroLeafVolumeBudget

/-!
# Axiom audit for the finite fused zero-coordinate CW volume bound

The source is certificate-independent, but this audit lives beside the other total-weight volume
budget audits because that is its sole intended consumer.
-/

namespace MatrixMultiplication.CoppersmithWinogradZeroLeafVolumeBudget

#assert_axioms nominalVolumeBits
#assert_axioms nativeDimensionProduct_eq_familyDimension
#assert_axioms two_rpow_nominalVolumeBits_le_typeClassEntropyLoss_mul_familyDimension
#assert_axioms two_rpow_nominalVolumeBits_le_typeClassEntropyLoss_mul_nativeDimensionProduct

end MatrixMultiplication.CoppersmithWinogradZeroLeafVolumeBudget
