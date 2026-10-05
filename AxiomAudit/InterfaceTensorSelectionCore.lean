/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorSelectionCore
import AxiomAudit.Command

/-! Axiom audit for finite exact-profile selection. -/

open AlgebraicComplexity
open AlgebraicComplexity.Tensor

#assert_axioms CompleteSplitProfile.matchesPositiveWord_iff_isConsistent
#assert_axioms CompleteSplitProfile.matchesEncodedPositiveWord_iff
#assert_axioms CompleteSplitProfile.singleton_matchesEncodedPositiveWord_zero_iff
#assert_axioms ExactInterfaceTermParameters.positivePowerProfile
#assert_axioms PartitionedTensor.selectCompleteSplitProfiles
#assert_axioms PartitionedTensor.mem_selectCompleteSplitProfiles_support
#assert_axioms PartitionedTensor.selectExactInterfaceTerm
#assert_axioms PartitionedTensor.selectEncodedCompleteSplitProfiles
#assert_axioms PartitionedTensor.mem_selectEncodedCompleteSplitProfiles_support
#assert_axioms PartitionedTensor.selectEncodedExactInterfaceTerm
