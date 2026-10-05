/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.IndexedTauWeight

set_option autoImplicit false

/-! # Axiom audit for indexed tau-weight additivity -/

#assert_axioms AlgebraicComplexity.HasTauWeight.map_linearEquiv
#assert_axioms AlgebraicComplexity.HasTauWeight.indexedDirectSum
#assert_axioms AlgebraicComplexity.HasTauWeight.indexedDirectSum_of_forall
