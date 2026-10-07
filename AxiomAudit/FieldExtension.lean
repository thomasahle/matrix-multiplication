/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.FieldExtension

set_option autoImplicit false

/-!
# Axiom audit for change of scalars in the exponent

Focused trust audit for `MatrixMultiplication/FieldExtension.lean`: base change of
matrix-multiplication rank and of `omega` along a ring homomorphism, specialization of a bilinear
algorithm over a field extension to a finite one, descent along a finite extension, and the
theorem that `omega` depends only on the characteristic.
-/

namespace AlgebraicComplexity

#assert_axioms BilinearAlgorithm.Computes.mapCoeff
#assert_axioms rankLE_matrixMultiplication_of_ringHom
#assert_axioms omega_le_of_ringHom
#assert_axioms omega_le_omega_nat
#assert_axioms omega_le_omega_int
#assert_axioms BilinearAlgorithm.exists_computes_of_finiteDimensional
#assert_axioms BilinearAlgorithm.exists_finiteDimensional_computes
#assert_axioms rankLE_matrixMultiplication_pow_of_fieldExtension
#assert_axioms rpow_omega_le_of_rankLE_of_fieldExtension
#assert_axioms omega_le_of_fieldExtension
#assert_axioms omega_eq_of_fieldExtension
#assert_axioms omega_algebraicClosure
#assert_axioms omega_le_of_forall_isAlgClosed
#assert_axioms omega_eq_omega_rat
#assert_axioms omega_eq_omega_zmod
#assert_axioms omega_eq_of_charP
#assert_axioms omega_complex

end AlgebraicComplexity
