/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivisionIterated

/-! # Axiom audit for the iterated regional division of a localized segmented leaf

`[duan2023faster]`'s `claim:degen` iterated over an arbitrary finite list of consecutive regions,
fused with the weight law so that no iterated external product is named.

Exact source lines: `papers/sources/2210.10173/component_value.tex:18-24` (`claim:degen`).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.SegmentRegionSpec
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.size
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.type
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.value
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.total
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.total_nil
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.total_cons
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.parentType
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.parentType_nil
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.parentType_cons
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.totalValue
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.totalValue_nil
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.totalValue_cons
#assert_axioms AlgebraicComplexity.SegmentRegionSpec.totalValue_nonneg
#assert_axioms AlgebraicComplexity.SegmentedRegionalWeights
#assert_axioms AlgebraicComplexity.hasTauWeight_segmentedLocalizedSplittingPower_regional
