/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationCTensor
import AxiomAudit.Command

/-!
# Axiom audit for exact zero-coordinate CW C-tensor retyping in every orientation

Checks the three rotated ambient retypings and the three restrictions of the rotated interface
tensor onto its canonically enumerated C-tensor, one per zero orientation.  The zero-`Z` pair is
checked beside the committed unrotated one, so this client records that the generic transport
specializes to the committed construction.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwSelectedExactInterfaceTerm_zeroX_ambientFiberRetyping
#assert_axioms cwSelectedExactInterfaceTerm_zeroX_restricts_rotatedAmbientCTensor
#assert_axioms cwSelectedExactInterfaceTerm_zeroY_ambientFiberRetyping
#assert_axioms cwSelectedExactInterfaceTerm_zeroY_restricts_rotatedAmbientCTensor
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_rotatedAmbientFiberRetyping
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_restricts_rotatedAmbientCTensor
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_ambientFiberRetyping
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_restricts_ambientCTensor
