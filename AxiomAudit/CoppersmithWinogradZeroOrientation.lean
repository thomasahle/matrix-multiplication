/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientation
import AxiomAudit.Command

/-!
# Axiom audit for exact zero-coordinate CW interfaces in every orientation

Checks the orientation-indexed CW shared-leg support law and its three named specializations, plus
the two orientation-free CW inputs the instantiation consumes: the native chunk encoding's
injectivity and the fine legality of the depth-`d` chunk support.

The zero-`Z` specialization is checked alongside the committed zero-`Z` theorem, so this client
also records that the two agree in the only sense that matters — both are provable, from the same
axioms, with the same statement.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! ## The orientation-free CW inputs -/

#assert_axioms cwChunkSplitWord_injective
#assert_axioms cwChunkPartitionedTensor_isEncodedFineLegalOnSupport
#assert_axioms cwChunkSplitWord_zeroChunkWord

/-! ## The support law and its three orientations -/

#assert_axioms cwSelectedExactInterfaceTerm_zero_support_isSharedFiber
#assert_axioms cwSelectedExactInterfaceTerm_zeroX_support_isSharedFiber
#assert_axioms cwSelectedExactInterfaceTerm_zeroY_support_isSharedFiber
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber'
