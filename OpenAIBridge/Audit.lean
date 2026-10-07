/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import OpenAIBridge.Consequences
import OpenAIBridge.NineQuarters
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
  `omega`, and the readings of that bound in `OpenAIBridge/Consequences.lean`.

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
#assert_axioms AlgebraicComplexity.OpenAIBridge.omega_lt
#assert_axioms AlgebraicComplexity.OpenAIBridge.rectangularOmega_le
#assert_axioms AlgebraicComplexity.OpenAIBridge.asymptoticRank_matrixMultiplication_le
#assert_axioms AlgebraicComplexity.OpenAIBridge.exists_straightline_matrixProduct
