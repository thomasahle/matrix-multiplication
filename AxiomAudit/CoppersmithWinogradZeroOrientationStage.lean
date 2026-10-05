/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationStage
import AxiomAudit.Command

/-!
# Axiom audit for family-level oriented zero-coordinate stages
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwSelectedExactInterfaceTerm_zero_fusedStage
#assert_axioms WholeConstituentLaserVolumeStage.mergeCWSelectedZeroFamily
