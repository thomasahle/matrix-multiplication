/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradNestedTotalWeightSupportEncoding
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Trust audit for the actual nested total-weight support encoding

These assertions audit the finite coordinate-legality and injective present-target encoding for
the level-two total-weight quotient used by the canonical Total-Weight certificate.  The source
passages are Definition `def:split-hatI` of [alman2025more],
`papers/sources/2404.16349/prelim.tex:225-232,249-269`, and the Total-Weight manuscript's
`eq:total-weight-tight`, `hyp:quotient-count`, `rem:quotient-count-nonexamples`, and
`rem:granularity-forced`, `better_bound/paper.tex:1290-1300,1729-1801`.

The audit covers only the actual-support encoder.  In particular, it does not assert the ambient
competitor family or either unproved clause of `hyp:quotient-count`.
-/

open AlgebraicComplexity.Examples

#assert_axioms cwDepthTwoTotalWeightPayload_sum_eq_coarseTotal
#assert_axioms cwRecursiveApproximateNestedTotalWeightTerm
#assert_axioms cwRecursiveApproximateNestedTotalWeightTerm_coarse_sum
#assert_axioms CWCoarseFieldEncoding.cwLevelFourNestedTotalWeightOrientedLegalTriple
#assert_axioms CWCoarseFieldEncoding.cwLevelFourNestedTotalWeightOrientedLegalTriple_injective
#assert_axioms CWCoarseFieldEncoding.cwLevelFourNestedTotalWeightPresentTargets
#assert_axioms CWCoarseFieldEncoding.card_cwLevelFourNestedTotalWeightPresentTargets
