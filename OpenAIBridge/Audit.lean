/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import OpenAIBridge.Consequences
import OpenAIBridge.NineQuarters
import OpenAIBridge.Rectangular
import OAI.LinearAlgebra.MatrixMultiplication.AllFields

set_option autoImplicit false

/-!
# Axiom audit for the vendored `ω ≤ 9/4` proof and its bridge

Enforcing trust audit for `OpenAIBridge/NineQuarters.lean` and for the theorems of the vendored
development in `ThirdParty/OAI/` that it rests on.  Every assertion fails the build unless the
declaration depends only on `propext`, `Classical.choice` and `Quot.sound`: nothing unproved, no
project axiom, no `native_decide`.

Three layers are asserted separately, so that a failure says where it is:

* the vendored exact-rank statements the bridge consumes;
* the vendored arithmetic-program statements (`OAI.MatrixMultiplication.omega_le_nine_quarters`
  and the explicit cost bound), which the bridge does not use but which are the theorems the
  upstream repositories publish;
* the bridge itself, ending in `omega_le_nine_quarters`, the statement about this repository's
  `omega`, and the readings of that bound in `OpenAIBridge/Consequences.lean`;
* the vendored rectangular statements over `ℂ` (`ω(0.709) < 2.092` and `α > 0.465`, in the
  arithmetic-program model), the comparison of that model with tensor rank in
  `OpenAIBridge/ArithmeticPrograms.lean`, and the resulting statements about this repository's
  `rectangularOmega` and `rectangularAlpha` in `OpenAIBridge/Rectangular.lean`.

This file lives in the `OpenAIBridge` target rather than under `AxiomAudit/`, so that the main
build does not compile the vendored development.
-/

#assert_axioms OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_nine_quarters
#assert_axioms OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_algebraicClosure
#assert_axioms OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_nine_quarters_allFields
#assert_axioms OAI.MatrixMultiplication.AuxiliarySeparation.matrix_multiplication_cost_le
#assert_axioms OAI.MatrixMultiplication.omega_le_nine_quarters
#assert_axioms OAI.MatrixMultiplication.complex_omega_le_nine_quarters

#assert_axioms AlgebraicComplexity.OpenAIBridge.rankLE_matrixMultiplication_of_rankAtMost
#assert_axioms AlgebraicComplexity.OpenAIBridge.omega_le_exactRankExponent
#assert_axioms AlgebraicComplexity.OpenAIBridge.exactRankExponent_le_nine_quarters
#assert_axioms AlgebraicComplexity.OpenAIBridge.omega_le_nine_quarters
#assert_axioms AlgebraicComplexity.OpenAIBridge.omega_le_nine_quarters_of_isAlgClosed
#assert_axioms AlgebraicComplexity.OpenAIBridge.omega_le_nine_quarters_via_fieldExtension
#assert_axioms AlgebraicComplexity.OpenAIBridge.omega_lt
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_le
#assert_axioms AlgebraicComplexity.OpenAIBridge.asymptoticRank_matrixMultiplication_le
#assert_axioms AlgebraicComplexity.OpenAIBridge.exists_straightline_matrixProduct

#assert_axioms OAI.MatrixMultiplication.CW75ReorderedRectangular.rectangularOmega_lt_target
#assert_axioms OAI.MatrixMultiplication.DualExponentBound.fixedAspect_omega_eq_two
#assert_axioms OAI.MatrixMultiplication.DualExponentBound.alpha_gt

#assert_axioms AlgebraicComplexity.OpenAIBridge.toStraightline_eval
#assert_axioms AlgebraicComplexity.OpenAIBridge.mulOps_toStraightline
#assert_axioms AlgebraicComplexity.OpenAIBridge.rankLE_matrixMultiplication_of_matrixAlgorithm
#assert_axioms AlgebraicComplexity.OpenAIBridge.omega_le_arithmeticOmega
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_le_arithmeticRectangularOmega
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_complex_lt
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_complex_eq_two
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularAlpha_complex_gt
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_lt_of_charZero
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_eq_two_of_charZero
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularAlpha_gt_of_charZero
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_le_lowChord_of_charZero
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_le_highChord_of_charZero
