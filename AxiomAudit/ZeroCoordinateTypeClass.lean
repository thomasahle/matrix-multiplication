/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateTypeClass
import AxiomAudit.Command

/-! Axiom audit for exact zero-coordinate complete-fibre counting. -/

open AlgebraicComplexity

#assert_axioms ZeroCoordinateCompleteFiberData.encoded_x_blockAddress
#assert_axioms ZeroCoordinateCompleteFiberData.encoded_y_blockAddress
#assert_axioms ZeroCoordinateCompleteFiberData.encoded_z_blockAddress
#assert_axioms multiplicity_comp_complementSplitWord
#assert_axioms CompleteSplitProfile.isConsistent_zero_of_total_eq_zero
#assert_axioms ZeroCoordinateCompleteFiberData.blockAddress_mem_selectedSupport
#assert_axioms card_selectEncodedCompleteSplitProfiles_zero_eq_card_typeClass
