/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroDimension
import AxiomAudit.Command

/-! Axiom audit for exact zero-coordinate CW dimensions. -/

open AlgebraicComplexity
open AlgebraicComplexity.Examples

#assert_axioms cwSelectedExactInterfaceSupportedWord_letter_z_eq_zero
#assert_axioms cwSelectedExactInterfaceSupportedWord_x_isConsistent
#assert_axioms cwSelectedExactInterfaceSupportedWord_sum_middleCount
#assert_axioms cwSelectedExactInterfaceConstituentDimension_zeroZ
