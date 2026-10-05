/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradUniversalBarrier

set_option autoImplicit false

/-!
# Axiom audit for the unconditional `CW` universal-method barrier

Focused trust audit for the `Unconditional` section of
`AlgebraicComplexity/Examples/GeneralizedCoppersmithWinogradUniversalBarrier.lean`, the `CW`
instance of Theorem 5.7 of J. Alman, *Limits on the Universal Method for Matrix Multiplication*,
PhD thesis, MIT, 2019: no generalized Coppersmith--Winograd tensor
([coppersmith1990matrix], Eq. (10)) proves a bound below `13/6` by the Universal method.

The umbrella audit asserts the two `Barrier`-section forms, which still take the packaged
`Tensor.SliceRankDegenerationMonotone` as an explicit binder.  Asserted here are the two primed
forms the `README.md` Results row names as the unconditional statements; they discharge the
binder through `Tensor.sliceRankDegenerationMonotone_holds`, audited in
`AxiomAudit/SliceRankDegeneration.lean`.
-/

namespace AlgebraicComplexity.Examples

#assert_axioms thirteen_div_six_le_universalExponent_gcwTable'
#assert_axioms two_lt_universalExponent_gcwTable'

end AlgebraicComplexity.Examples
