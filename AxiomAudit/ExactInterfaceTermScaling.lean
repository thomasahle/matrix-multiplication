/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceTermScaling

/-! # Axiom audit for exact interface-term scaling -/

#assert_axioms AlgebraicComplexity.CompleteSplitProfile.scale_toDistribution
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.scale
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.scale_multiplicity
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.scale_index
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.scale_split_counts
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.scale_multiplicity_pos
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.scale_toSemantic_split
