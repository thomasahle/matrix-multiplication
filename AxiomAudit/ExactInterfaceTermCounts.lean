/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceTermCounts

/-!
# Axiom audit for exact interface terms built from count rows

The constructors package either three integral count rows or the three pushforwards of one finite
source row as the exact interface-term parameters consumed by recursive certificate clients.
These assertions keep their observable data, count-table semantics, and source-word consistency
bridge inside the project's allowlisted foundational axioms.
-/

#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.ofCountRows_multiplicity
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.ofCountRows_index
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.ofCountRows_split_counts
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.ofMappedCountRows_multiplicity
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.ofMappedCountRows_index
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.ofMappedCountRows_split_counts
#assert_axioms AlgebraicComplexity.ExactInterfaceTermParameters.ofMappedCountRows_split_isConsistent
