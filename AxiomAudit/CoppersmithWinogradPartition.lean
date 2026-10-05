/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradPartition

set_option autoImplicit false

/-!
# Axiom audit for the typed partitioned realization of `CW_q`

Focused trust audit for `AlgebraicComplexity/Examples/CoppersmithWinogradPartition.lean` and for
the corner-removing monomial degeneration of
`AlgebraicComplexity/Examples/CoppersmithWinograd.lean`, both formalizing the tensor of
[coppersmith1990matrix], Eq. (10).

`AxiomAudit/CoppersmithWinogradBorderRank.lean` asserts the border-rank statements carried across
the partition isomorphism. The assertions below cover the monomial degeneration onto the
middle block, the canonical isomorphism of the six-block realization, the six certified
rectangular constituents together with their volume, and the match between the partitioned laser
log-value and the support laser log-value. The three coordinate-projection identities in the
base CW module are asserted directly as well, covering their LIB-55 proof-only simplification.
-/

namespace AlgebraicComplexity.Examples

#assert_axioms coppersmithWinograd_monomialDegenerates_middle
#assert_axioms map_cw011Map_coppersmithWinograd
#assert_axioms map_cw101Map_coppersmithWinograd
#assert_axioms map_cw110Map_coppersmithWinograd
#assert_axioms cwPartitionedTensor_isomorphic
#assert_axioms cwPartitionedMMCertificate
#assert_axioms cwPartitionedMMCertificate_volume
#assert_axioms cwPartitionedLaserLogValue_eq_supportLaserLogValue

end AlgebraicComplexity.Examples
