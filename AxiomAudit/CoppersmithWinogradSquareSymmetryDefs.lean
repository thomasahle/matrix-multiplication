/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareSymmetryDefs
import AxiomAudit.Command

/-!
# Axiom audit for the base CW constituent symmetries

Checks the two retypings and the two symmetry theorems that
`Examples/CoppersmithWinogradSquareSymmetryDefs.lean` carries: cycling and `Y`/`Z`-swapping a
supported base Coppersmith--Winograd constituent lands on the constituent with the corresponding
block labels permuted.

The audit imports the definition module directly, not the squared-tensor module above it, so a
failure here is attributable to the base half alone.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! ## The two retypings -/

#assert_axioms cwBaseConstituentCycleEquiv
#assert_axioms cwBaseConstituentSwapEquiv

/-! ## The two base symmetry theorems -/

#assert_axioms cwConstituentOfBlocks_cycle
#assert_axioms cwConstituentOfBlocks_swap
