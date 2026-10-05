/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DiscoveredDecompositions

set_option autoImplicit false

/-!
# Axiom audit for the characteristic-two flip-graph decomposition of `⟨3,2,3⟩`

Focused trust audit for `AlgebraicComplexity/Examples/DiscoveredDecompositions.lean`, whose
search-produced tables are re-checked by the Lean kernel over every commutative ring in which
`2 = 0`; the search follows M. Kauers and J. Moosbauer, *Flip graphs for matrix multiplication*,
ISSAC 2023.

The umbrella audit asserts the harness, the two rank certificates over a general ring, and the
`ZMod 2` instance for `⟨3,3,3⟩`.  Asserted here is the second `ZMod 2` instance that the
`README.md` Results row names, `rankLE_three_two_three_zmod`.
-/

namespace AlgebraicComplexity.Examples.DiscoveredDecompositions

#assert_axioms rankLE_three_two_three_zmod

end AlgebraicComplexity.Examples.DiscoveredDecompositions
