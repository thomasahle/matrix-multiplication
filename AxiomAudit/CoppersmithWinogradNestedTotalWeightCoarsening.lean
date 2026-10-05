/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradNestedTotalWeightCoarsening
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Trust audit for nested level-four total-weight labels

These assertions cover the structural level-two total-weight refinement used for the consecutive
block hierarchy in the “Leveled Partition for Large Tensor Powers” and “Complete Split
Distributions” subsections of [alman2025more], including Definition `def:split-hatI`,
`papers/sources/2404.16349/prelim.tex:225-232,249-269`, and Remark
`rem:granularity-forced` of the Total-Weight manuscript,
`better_bound/paper.tex:1783-1800`.
-/

open AlgebraicComplexity.Examples

#assert_axioms CWDepthTwoTotalWeightPayload
#assert_axioms CWDepthTwoTotalWeightPayload.outer
#assert_axioms cwDepthTwoTotalWeightPayload
#assert_axioms cwDepthTwoTotalWeightPayload_outer
#assert_axioms CWLevelFourNestedTotalWeightIndex
#assert_axioms CWLevelFourNestedTotalWeightWord
#assert_axioms CWLevelFourNestedTotalWeightAddress
#assert_axioms cwLevelFourNestedTotalWeightWord
#assert_axioms cwLevelFourNestedTotalWeightCoarsening
#assert_axioms cwLevelFourNestedOuterWord
#assert_axioms cwLevelFourNestedOuterAddress
#assert_axioms cwLevelFourNestedOuterWord_map
#assert_axioms cwLevelFourNestedOuterAddress_coarsen
