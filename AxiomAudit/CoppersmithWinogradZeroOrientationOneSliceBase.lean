/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationOneSliceBase
import AxiomAudit.Command

/-!
# Axiom audit for the zero-`X` and zero-`Y` one-slice bases

Checks the third rotation of the supported base Coppersmith--Winograd constituents, the three
transport constructors it feeds, the six new base certificates for the `cw002` / `cw011` / `cw101`
families in the two non-canonical orientations, and the leg-indexed form that recovers the
committed zero-`Z` construction at `zero = .Z`.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! ## The third rotation -/

#assert_axioms cwBaseConstituentCycleSymmEquiv
#assert_axioms cwConstituentOfBlocks_cycleSymm

/-! ## The transports -/

#assert_axioms cwRotatedBaseOfCycle
#assert_axioms cwRotatedBaseOfCycleSymm
#assert_axioms cwRotatedBaseOfRefl

/-! ## The six new base certificates -/

#assert_axioms cw020ZeroXOneSliceRestriction
#assert_axioms cw002ZeroXOneSliceRestriction
#assert_axioms cw011ZeroXOneSliceRestriction
#assert_axioms cw200ZeroYOneSliceRestriction
#assert_axioms cw002ZeroYOneSliceRestriction
#assert_axioms cw101ZeroYOneSliceRestriction

/-! ## The leg-indexed base certificate -/

#assert_axioms cwZeroBaseRotatedOneSliceRestriction
