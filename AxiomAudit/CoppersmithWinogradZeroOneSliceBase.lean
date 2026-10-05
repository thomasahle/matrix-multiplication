/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSliceBase
import AxiomAudit.Command

/-!
# Axiom audit for the zero-coordinate CW base one-slice certificates

Checks the three explicit base coordinate maps, their exact tensor identities, and the explicit
one-slice restriction certificates they carry.  The separately compiled `200`, `020`, and `110`
proofs are audited here through the single re-exporting base module.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cw200OneSliceIndex
#assert_axioms cw200OneSliceMap
#assert_axioms cw020OneSliceIndex
#assert_axioms cw020OneSliceMap
#assert_axioms cw110OneSliceIndex
#assert_axioms cw110OneSliceMap
#assert_axioms map_cw200OneSliceMap
#assert_axioms map_cw020OneSliceMap
#assert_axioms map_cw110OneSliceMap
#assert_axioms cw200OneSliceRestriction
#assert_axioms cw020OneSliceRestriction
#assert_axioms cw110OneSliceRestriction
