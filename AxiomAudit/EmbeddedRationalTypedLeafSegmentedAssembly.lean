/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.EmbeddedRationalTypedLeafSegmentedAssembly

/-! Focused axiom audit for sparse typed-leaf segment assembly. -/

#assert_axioms AlgebraicComplexity.RationalTypedLeaf.positiveSupportWordTensor_matrixMultiplication_proportional_embedded
#assert_axioms AlgebraicComplexity.RationalTypedLeaf.embeddedSegmentedCertificate
