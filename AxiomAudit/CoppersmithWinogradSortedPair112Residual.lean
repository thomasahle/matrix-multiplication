/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPair112Residual

set_option autoImplicit false

/-!
# Axiom audit for the sorted-pair `(112)` residual bridge

This companion checks the exact two-address support, its four-address fine preimage, the
coarsening isomorphism, and the restriction onto `cw112PartitionedTensor`.  The mathematical
decomposition is `[almanwilliams2024refined]`,
`papers/sources/2010.05846/final-TheoretiCS.tex:613-629`; the proposed sorted-pair quotient and
the separate entropy-accounting obligation are `better_bound/paper.tex:2664-2673` and
`:1622-1648`.

No entropy, word-level grouping, value estimate, or exponent endpoint is audited here because
the source module proves none.
-/

#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualSupport
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualSupport_preimage
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualCut_isomorphic_fineFiber
#assert_axioms AlgebraicComplexity.Examples.cwSortedPair112ResidualCut_restricts_partitioned
