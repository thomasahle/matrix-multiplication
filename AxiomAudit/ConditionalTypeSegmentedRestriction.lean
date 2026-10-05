/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.ConditionalTypeSegmentedRestriction

set_option autoImplicit false

/-!
# Axiom audit for conditional types as segmented restrictions

The audited spelling bridge supports the fully path-tagged inner-stage family of the Total-Weight
method (`better_bound/paper.tex:1715-1775`) and the complete-split condition preceding Claim 6.18
of [alman2025more] (`papers/sources/2404.16349/constituent.tex:376-440`).
-/

namespace AlgebraicComplexity.WordType

#assert_axioms finiteCellSegmentation
#assert_axioms segmentMultiplicity_finiteCellSegmentation
#assert_axioms mem_conditionalTypeClass_iff_segmentMultiplicity

end AlgebraicComplexity.WordType
