/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorExactCore
import AxiomAudit.Command

/-! Axiom audit for exact finite interface data. -/

open AlgebraicComplexity

#assert_axioms CompleteSplitProfile.typeClass
#assert_axioms CompleteSplitProfile.singleton
#assert_axioms CompleteSplitProfile.singleton_counts
#assert_axioms CompleteSplitProfile.isConsistent_comp_perm
#assert_axioms CompleteSplitProfile.isConsistent_iff_mem_typeClass
#assert_axioms CompleteSplitProfile.singleton_isConsistent_const_iff
#assert_axioms LevelConstituentIndex
#assert_axioms ExactInterfaceTermParameters
