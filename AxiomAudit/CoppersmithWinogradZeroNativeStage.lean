/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroNativeStage
import AxiomAudit.Command

/-!
# Axiom audit for native-frame zero-coordinate CW stages
-/

open AlgebraicComplexity.Examples

#assert_axioms cwSelectedZeroFamilyDimension
#assert_axioms cwSelectedExactInterfaceTerm_zero_nativeStage
