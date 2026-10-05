/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationFusion
import AxiomAudit.Command

/-!
# Axiom audit for the three-orientation zero-coordinate CW fusion

Checks the leg-indexed interface exponent and its two consistency laws, the rotated interface
constituent certificate, the shared-fibre datum it feeds, and the fusion theorem in all three
orientations.  The zero-`Z` instance is checked too: it is what certifies that the leg-indexed
fusion subsumes the committed one.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! ## The leg-indexed exponent -/

#assert_axioms cwZeroInterfaceQExponentOn
#assert_axioms cwZeroInterfaceQExponentOn_X
#assert_axioms cwSelectedExactInterfaceSupportedWord_isConsistent
#assert_axioms cwSelectedExactInterfaceSupportedWord_sum_middleCount_on

/-! ## The rotated interface constituent, and the fusion -/

#assert_axioms cwSelectedExactInterfaceConstituentRotatedCoherentRestriction
#assert_axioms cwSelectedExactInterfaceTerm_zero_permutedSharedOneSliceData
#assert_axioms cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice
#assert_axioms cwSelectedExactInterfaceTerm_zeroX_restricts_fusedOneSlice
#assert_axioms cwSelectedExactInterfaceTerm_zeroY_restricts_fusedOneSlice
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_restricts_rotatedFusedOneSlice
