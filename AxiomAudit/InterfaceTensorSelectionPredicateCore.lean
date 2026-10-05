/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorSelectionPredicateCore
import AxiomAudit.Command

/-! Axiom audit for exact-profile predicates on positive words. -/

open AlgebraicComplexity

#assert_axioms CompleteSplitProfile.matchesPositiveWord_iff_isConsistent
#assert_axioms CompleteSplitProfile.matchesEncodedPositiveWord_iff
#assert_axioms CompleteSplitProfile.singleton_matchesEncodedPositiveWord_zero_iff
#assert_axioms ExactInterfaceTermParameters.positivePowerProfile
