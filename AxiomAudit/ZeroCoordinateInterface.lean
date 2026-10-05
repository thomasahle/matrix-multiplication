/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateInterface
import AxiomAudit.Command

/-!
# Axiom audit for exact zero-coordinate interface supports

Checks the generic shared-leg support law and the four coordinatewise steps it is built from:
the constant native word on a zero-count leg, the digitwise complement of the encoded chunks,
and the two directions of side-block determination.
-/

open AlgebraicComplexity AlgebraicComplexity.MoreAsymmetryCompatibility

#assert_axioms completeSplitProfile_weight_eq_of_isConsistent
#assert_axioms selectedExactInterfaceTerm_chunkWeight
#assert_axioms selectedExactInterfaceTerm_leg_eq_const_of_count_eq_zero
#assert_axioms selectedExactInterfaceTerm_yChunk_eq_complement_xChunk_of_z_eq_zero
#assert_axioms selectedExactInterfaceTerm_y_eq_of_x_eq_of_z_eq_zero
#assert_axioms selectedExactInterfaceTerm_x_eq_of_y_eq_of_z_eq_zero
#assert_axioms selectedExactInterfaceTerm_zeroZ_support_isSharedFiber
