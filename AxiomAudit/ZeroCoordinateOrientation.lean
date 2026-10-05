/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientation
import AxiomAudit.Command

/-!
# Axiom audit for zero-coordinate interface supports in every orientation

Checks the orientation-indexed shared-leg support law, the single complement law that replaces the
three committed ones, the two directions of live-block determination, and the leg-convention layer
(the two live legs, their distinctness, the leg trichotomy, and the normalizing rotation with its
six bridge lemmas).

The three named orientations are checked as well, including the zero-`Z` re-derivation, which is
what certifies that the generic law subsumes the committed `Z`-only statement.
-/

open AlgebraicComplexity AlgebraicComplexity.MoreAsymmetryCompatibility

/-! ## The leg-convention layer -/

#assert_axioms firstLiveLeg_ne_self
#assert_axioms secondLiveLeg_ne_self
#assert_axioms secondLiveLeg_ne_firstLiveLeg
#assert_axioms leg_eq_or_eq_firstLiveLeg_or_eq_secondLiveLeg

#assert_axioms zeroOrientation_zero
#assert_axioms zeroOrientation_firstLiveLeg
#assert_axioms zeroOrientation_secondLiveLeg
#assert_axioms zeroOrientation_symm_Z
#assert_axioms zeroOrientation_symm_X
#assert_axioms zeroOrientation_symm_Y
#assert_axioms zeroOrientation_Z

/-! ## The rotated complement law and the support law -/

#assert_axioms
  CompatibilityModel.secondLiveChunk_eq_complement_firstLiveChunk_of_get_eq_zero
#assert_axioms selectedExactInterfaceTerm_secondLiveChunk_eq_complement_firstLiveChunk
#assert_axioms selectedExactInterfaceTerm_secondLiveLeg_eq_of_firstLiveLeg_eq
#assert_axioms selectedExactInterfaceTerm_firstLiveLeg_eq_of_secondLiveLeg_eq
#assert_axioms selectedExactInterfaceTerm_zero_support_isSharedFiber

/-! ## The three orientations -/

#assert_axioms selectedExactInterfaceTerm_zeroX_support_isSharedFiber
#assert_axioms selectedExactInterfaceTerm_zeroY_support_isSharedFiber
#assert_axioms selectedExactInterfaceTerm_zeroZ_support_isSharedFiber'
